-- Prove2me | solution 1 for ConsistentSubmodular.Chains.xiStar_le_adaptivityGap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:40:11.639605+00:00
-- url     : https://prove2.me/submissions/40439a4e-cc29-40fa-ae09-21a90375c977

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_chainValue_le
import Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff
import Theorems.Thm_ConsistentSubmodular_Chains_adaptivityGap_eq
import Theorems.Thm_ConsistentSubmodular_Chains_expectedLeft_eq

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem chainValue_cons_cons (x y : ℝ) (rest : List ℝ) :
    chainValue (x :: y :: rest) = edgeValue x y + chainValue (y :: rest) := rfl

theorem chainValue_ofFn {N : ℕ} (z : Fin (N + 1) → ℝ) :
    chainValue (List.ofFn z) = ∑ j : Fin N, edgeValue (z j.castSucc) (z j.succ) := by
  induction N with
  | zero => simp [chainValue]
  | succ N ih =>
    rw [List.ofFn_succ, List.ofFn_succ, chainValue_cons_cons, Fin.sum_univ_succ]
    have h := ih (fun i => z i.succ)
    rw [List.ofFn_succ] at h
    rw [h]
    rfl

/-- **Inequality (14)**: for a chain `d_0 ≥ ... ≥ d_N = 1`,
`Σ_j (1 - d_{j+1}/d_j) - q Σ_j (d_j - 1) = Σ_j φ(d_j, d_{j+1}) ≤ q`. -/
theorem sum_edgeValue_le {N : ℕ} (d : Fin (N + 1) → ℝ) (hanti : Antitone d)
    (hlast : d (Fin.last N) = 1) :
    ∑ j : Fin N, edgeValue (d j.castSucc) (d j.succ) ≤ qStar := by
  rw [← chainValue_ofFn]
  apply chainValue_le
  refine ⟨List.isChain_ofFn.mpr fun i hi => hanti (Fin.mk_le_mk.mpr (by omega)), ?_, ?_⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    rw [← hlast]
    exact hanti (Fin.le_last i)
  · rw [List.getLast?_eq_some_getLast (by simp), List.getLast_ofFn, ← hlast]
    rfl

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem sum_Iic_eq {N : ℕ} (f : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i, if i ≤ j then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)

include hI

theorem length_antitone : Antitone (intervalLength I) :=
  Fin.antitone_iff_succ_le.mpr fun i => hI.2.2.1 i

theorem length_pos (j : Fin (N + 1)) : 0 < intervalLength I j :=
  lt_of_lt_of_le hI.2.2.2 (length_antitone hI (Fin.le_last j))

end Consecutive

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)

include hI

/-- `C = E[d_j] ≥ d_N`. -/
theorem length_last_le_expectedLength :
    intervalLength I (Fin.last N) ≤ ∑ j, I.prob j * intervalLength I j := by
  calc intervalLength I (Fin.last N) = ∑ j, I.prob j * intervalLength I (Fin.last N) := by
        rw [← Finset.sum_mul, I.prob_sum, one_mul]
    _ ≤ ∑ j, I.prob j * intervalLength I j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (length_antitone hI (Fin.le_last j)) (I.prob_nonneg j)

end Consecutive

section Equalizing

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)

include hI hE

/-- The cumulative probabilities (5) of the equalizing distribution. -/
theorem cumulative_prob (i : Fin (N + 1)) :
    ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i :=
  (isEqualizing_iff hI).mp hE i

theorem prob_zero : I.prob 0 = intervalLength I (Fin.last N) / intervalLength I 0 := by
  have h : ∑ i ∈ Finset.Iic 0, I.prob i = intervalLength I (Fin.last N) / intervalLength I 0 :=
    cumulative_prob hI hE 0
  rw [sum_Iic_eq] at h
  rw [← h, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [if_neg]
    rw [Fin.le_iff_val_le_val]
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp only [Fin.val_zero]
    omega
  · simp

theorem prob_succ (j : Fin N) :
    I.prob j.succ = intervalLength I (Fin.last N) / intervalLength I j.succ -
      intervalLength I (Fin.last N) / intervalLength I j.castSucc := by
  have h1 : ∑ i ∈ Finset.Iic j.succ, I.prob i =
      intervalLength I (Fin.last N) / intervalLength I j.succ := cumulative_prob hI hE j.succ
  have h2 : ∑ i ∈ Finset.Iic j.castSucc, I.prob i =
      intervalLength I (Fin.last N) / intervalLength I j.castSucc := cumulative_prob hI hE j.castSucc
  rw [sum_Iic_eq] at h1 h2
  rw [← h1, ← h2, ← Finset.sum_sub_distrib, Finset.sum_eq_single j.succ]
  · rw [if_pos le_rfl, if_neg (not_le.mpr Fin.castSucc_lt_succ), sub_zero]
  · intro b _ hb
    split_ifs with hb1 hb2 hb2
    · ring
    · exfalso
      rw [Fin.le_iff_val_le_val] at hb1 hb2
      simp only [Fin.val_succ, Fin.val_castSucc] at hb1 hb2
      exact hb (Fin.ext (by simp only [Fin.val_succ]; omega))
    · exfalso
      rw [Fin.le_iff_val_le_val] at hb1 hb2
      simp only [Fin.val_succ, Fin.val_castSucc] at hb1 hb2
      omega
    · ring
  · simp

/-- `C = E[d_j] = d_N (1 + Σ_j (1 - d_{j+1}/d_j))`. -/
theorem expectedLength_eq : ∑ j, I.prob j * intervalLength I j =
    intervalLength I (Fin.last N) + intervalLength I (Fin.last N) *
      ∑ j : Fin N, (1 - intervalLength I j.succ / intervalLength I j.castSucc) := by
  rw [Fin.sum_univ_succ, prob_zero hI hE, div_mul_cancel₀ _ (length_pos hI 0).ne', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prob_succ hI hE]
  have h1 := (length_pos hI j.succ).ne'
  have h2 := (length_pos hI j.castSucc).ne'
  field_simp

end Equalizing

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

theorem solution : xiStar ≤ I.adaptivityGap := by
  set dN := intervalLength I (Fin.last N) with hdN
  have hdN0 : 0 < dN := length_pos hI (Fin.last N)
  have hchain := sum_edgeValue_le (fun j => intervalLength I j / dN)
    (fun i j hij => div_le_div_of_nonneg_right (length_antitone hI hij) hdN0.le)
    (div_self hdN0.ne')
  -- `d_N Σ_j φ(d_j / d_N, d_{j+1} / d_N) = (C - d_N) - q B`.
  have hscaled : dN * ∑ j : Fin N, edgeValue (intervalLength I j.castSucc / dN)
      (intervalLength I j.succ / dN) =
      dN * ∑ j : Fin N, (1 - intervalLength I j.succ / intervalLength I j.castSucc) -
        qStar * ∑ j : Fin N, (intervalLength I j.castSucc - dN) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := (length_pos hI j.castSucc).ne'
    unfold edgeValue
    field_simp
  have hB := expectedLeft_eq hI hE
  have hC := expectedLength_eq hI hE
  rw [← hdN] at hB hC
  have hineq : ∑ j, I.prob j * intervalLength I j - dN ≤
      qStar * (∑ j, I.prob j * I.left j + dN) := by
    have := mul_le_mul_of_nonneg_left hchain hdN0.le
    rw [hscaled] at this
    rw [hC, hB]
    nlinarith
  have hBnn : 0 ≤ ∑ j, I.prob j * I.left j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (I.prob_nonneg j) (I.left_nonneg j)
  have hCdN := length_last_le_expectedLength hI
  rw [← hdN] at hCdN
  rw [adaptivityGap_eq hI hE, ← hdN, le_div_iff₀ (by linarith), xiStar_eq_qStar]
  have hq := qStar_pos
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
  linarith

end
