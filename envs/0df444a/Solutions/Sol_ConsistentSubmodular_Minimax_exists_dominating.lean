-- Prove2me | solution 1 for ConsistentSubmodular.Minimax.exists_dominating
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:03.110664+00:00
-- url     : https://prove2.me/submissions/85d9ad07-c1da-4ab1-ad0b-12a27f81bfe1

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

/-- A continuous linear functional on `ℝ^{m+1}` is the pairing with its values on
the standard basis. -/
theorem functional_eq (f : Point m →L[ℝ] ℝ) (y : Point m) :
    f y = ∑ i, y i * f (Pi.single i 1) := by
  have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : Point m) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hy]
  simp [map_sum, map_smul]

end ConsistentSubmodular.Minimax

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Minimax
variable {m : ℕ}

theorem solution (w : Fin (m + 1) → Fin (m + 1) → ℝ) (v : ℝ)
    (h : ∀ b : Point m, IsSimplex b → ∃ i, v < ∑ j, b j * w i j) :
    ∃ a : Point m, IsSimplex a ∧ ∀ j, v < ∑ i, a i * w i j := by
  classical
  let K : Set (Point m) := rowSums w '' stdSimplex ℝ (Fin (m + 1))
  let T : Set (Point m) := Set.Iic fun _ => v
  have hK : IsCompact K :=
    (isCompact_stdSimplex ℝ (Fin (m + 1))).image
      (LinearMap.continuous_of_finiteDimensional (rowSums w))
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ (Fin (m + 1))).linear_image (rowSums w)
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hbT
    obtain ⟨i, hi⟩ := h b hb
    exact absurd (hbT i) (not_le.mpr hi)
  obtain ⟨f, u, u', hfK, huu', hfT⟩ :=
    geometric_hahn_banach_compact_closed hKc hK (convex_Iic _) isClosed_Iic hdisj
  -- The coefficients `c_i = -f(e_i)` are nonnegative, because `f` is bounded
  -- below on the orthant `T`.
  let c : Point m := fun i => -f (Pi.single i 1)
  have hv : u' < f fun _ => v := hfT _ Set.self_mem_Iic
  have hc (i : Fin (m + 1)) : 0 ≤ c i := by
    by_contra hneg
    have hpos : 0 < f (Pi.single i 1) := by
      simp only [c] at hneg
      linarith
    let t := (f (fun _ => v) - u') / f (Pi.single i 1)
    have hmem : ((fun _ => v) - t • (Pi.single i (1 : ℝ) : Point m)) ∈ T := by
      intro j
      have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
      have hsingle : (0 : ℝ) ≤ (Pi.single i (1 : ℝ) : Point m) j := by
        rw [Pi.single_apply]
        split_ifs <;> norm_num
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    have hval := hfT _ hmem
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at hval
    linarith
  have hf (y : Point m) : f y = -∑ i, c i * y i := by
    rw [functional_eq f y]
    simp only [c, neg_mul, Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- The coefficients are not all zero.
  have hS : 0 < ∑ i, c i := by
    rcases (Finset.sum_nonneg fun i _ => hc i).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hzero : ∀ i, c i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).mp heq.symm i
          (Finset.mem_univ i)
      have hK0 := hfK _ ⟨_, single_mem_stdSimplex ℝ 0, rfl⟩
      rw [hf] at hK0 hv
      simp only [hzero, zero_mul, Finset.sum_const_zero, neg_zero] at hK0 hv
      linarith
  set S := ∑ i, c i with hSdef
  refine ⟨fun i => c i / S, ⟨fun i => div_nonneg (hc i) hS.le, ?_⟩, fun j => ?_⟩
  · rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  · -- The column `j` is the row-sum vector of the vertex `e_j`.
    have hcol : rowSums w (Pi.single j 1) = fun i => w i j := by
      ext i
      simp [rowSums, Pi.single_apply]
    have hKj := hfK _ ⟨_, single_mem_stdSimplex ℝ j, rfl⟩
    rw [hcol, hf] at hKj
    rw [hf] at hv
    have hvS : ∑ i, c i * v = v * S := by
      rw [hSdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hvS] at hv
    have hsum : v * S < ∑ i, c i * w i j := by linarith
    have heq : ∑ i, c i / S * w i j = (∑ i, c i * w i j) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    show v < ∑ i, c i / S * w i j
    rw [heq, lt_div_iff₀ hS]
    linarith

end
