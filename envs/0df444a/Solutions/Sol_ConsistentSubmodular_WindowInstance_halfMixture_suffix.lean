-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.halfMixture_suffix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:20.519321+00:00
-- url     : https://prove2.me/submissions/9e83c71d-313c-40f5-8614-6e400d0c0b7f

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem benchmark_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.benchmark j :=
  W.objective.nonnegative _

theorem benchmark_mono : Monotone W.benchmark := by
  intro s j hsj
  unfold benchmark
  exact (W.objective.monotone _ _ (Finset.union_subset_union_right (W.arrivals_mono hsj))).trans
    (W.candidate_optimal j _ (W.candidate_subset s) (W.candidate_card s))

theorem benchmark_eq (j : Fin (W.lastStage + 1)) : W.benchmark j = W.arrivalValue j + W.gain j := by
  simp [gain]

/-- The optimum grows no faster than the arrivals alone, the second chain of
(19): `P_j - P_s ≤ λ_j - λ_s` for `s ≤ j`. The candidate `O_j` is feasible at
stage `s`, and diminishing returns compare the arrivals with and without it. -/
theorem benchmark_growth {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) :
    W.benchmark j - W.benchmark s ≤ W.arrivalValue j - W.arrivalValue s := by
  have hopt := W.candidate_optimal s (W.candidate j) (W.candidate_subset j) (W.candidate_card j)
  have hdr := W.objective.diminishing_returns
    (Finset.subset_union_right : W.arrivals s ⊆ W.candidate j ∪ W.arrivals s) (W.arrivals j)
  have h1 : (W.candidate j ∪ W.arrivals s) ∪ W.arrivals j = W.candidate j ∪ W.arrivals j := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr (W.arrivals_mono hsj)]
  rw [h1, Finset.union_eq_right.mpr (W.arrivals_mono hsj)] at hdr
  unfold benchmark arrivalValue
  linarith

theorem gain_antitone {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) : W.gain j ≤ W.gain s := by
  have h := W.benchmark_growth hsj
  unfold gain
  linarith

end WindowInstance

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- `r_j ≥ 0`, by monotonicity. -/
theorem residual_nonneg (i j : Fin (W.lastStage + 1)) : 0 ≤ W.residual i j := by
  unfold residual arrivalValue
  linarith [W.objective.monotone _ _
    (Finset.subset_union_left : W.arrivals j ⊆ W.arrivals j ∪ W.candidate i)]

/-- Inequality (26): the credit never exceeds the benchmark, `K_j ≤ P_j`. -/
theorem credit_le_benchmark (j : Fin (W.lastStage + 1)) : W.credit j ≤ W.benchmark j := by
  have hg := W.gain_antitone (Fin.zero_le j)
  have hA : W.objective.value (W.candidate 0) ≤
      W.objective.value (W.arrivals j ∪ W.candidate 0) :=
    W.objective.monotone _ _ Finset.subset_union_right
  have h0 := W.objective.nonnegative ∅
  have hz : W.gain 0 = W.objective.value (W.candidate 0) - W.objective.value ∅ := by
    simp [gain, benchmark, arrivalValue, W.arrivals_zero]
  unfold credit residual
  unfold gain at *
  linarith

end WindowInstance

/-- Lemma B.6 (suffix bound), the inequality (30) with `M` any upper bound of
`u` and `z` in place of `max(u, z)`. -/
theorem suffix_bound {lam g u z M γ : ℝ} (hz : 0 ≤ z) (hMu : u ≤ M) (hMz : z ≤ M)
    (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 2) (h : 2 * g - u ≤ γ * (lam + z)) :
    2 * (lam + g) ≤ (2 + γ) * (lam + (u + z + M) / 4) := by
  rcases le_total u z with huz | hzu
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMz),
      mul_nonneg (sub_nonneg.mpr hγ2) (show 0 ≤ 2 * z - u by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMu),
      mul_nonneg hγ0 (sub_nonneg.mpr hzu), mul_nonneg (sub_nonneg.mpr hγ2) hz]

/-- The suffix ratio `1/(2β)` dominates every level `α` with `2 β α ≤ 1`. -/
theorem le_of_suffix_ratio {α β P X : ℝ} (hβ : 0 < β) (hα : 2 * β * α ≤ 1) (hP : 0 ≤ P)
    (h : 2 * P ≤ 4 * β * X) : α * P ≤ X := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hα) hP, mul_pos hβ (sub_pos.mpr hlt)]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The envelope is attained at an eligible stage `h`: `K_h ≥ D`, because
`K_h ≤ P_h` (26). Hence the last eligible index `c` of (27) exists. -/
theorem exists_envelope_eligible {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ h, W.envelopeTerm β h = W.envelope β ∧ W.envelope β ≤ W.credit h := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (W.envelopeTerm β)
  refine ⟨h, hh.symm, ?_⟩
  rw [envelope, hh]
  have hK := W.credit_le_benchmark h
  have hP := W.benchmark_nonneg h
  simp only [envelopeTerm]
  nlinarith

end WindowInstance

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hafter : ∀ j, c < j → W.credit j < W.envelope β)
    {j : Fin (W.lastStage + 1)} (hcj : c < j) :
    α * W.benchmark j ≤ W.arrivalValue j +
      (W.residual 0 j + W.residual c j + max (W.residual 0 j) (W.residual c j)) / 4 := by
  have hγ : 0 ≤ 4 * β - 2 := by linarith
  obtain ⟨h, hh, hhK⟩ := W.exists_envelope_eligible hβ'
  have hhc : h ≤ c := by
    by_contra hn
    exact absurd hhK (not_le.mpr (hafter h (lt_of_not_ge hn)))
  -- The benchmark credit (31) of the partner: `D ≤ γ P_h ≤ γ P_c`.
  have hDP : W.envelope β ≤ (4 * β - 2) * W.benchmark c := by
    have hK := W.credit_le_benchmark h
    have hPh := mul_le_mul_of_nonneg_left (W.benchmark_mono hhc) hγ
    rw [← hh]
    simp only [ConsistentSubmodular.WindowInstance.envelopeTerm]
    nlinarith
  have hPc : W.benchmark c ≤ W.arrivalValue j + W.residual c j := by
    have hm := W.objective.monotone (W.candidate c ∪ W.arrivals c)
      (W.arrivals j ∪ W.candidate c) (by
        intro e he
        have hR := W.arrivals_mono hcj.le
        simp only [Finset.mem_union] at he ⊢
        rcases he with he | he
        · exact Or.inr he
        · exact Or.inl (hR he))
    simp only [ConsistentSubmodular.WindowInstance.residual, ConsistentSubmodular.WindowInstance.benchmark] at hm ⊢
    linarith
  have hK := hafter j hcj
  -- Last eligibility gives the premise (32) of Lemma B.6.
  have hpremise : 2 * W.gain j - W.residual 0 j ≤
      (4 * β - 2) * (W.arrivalValue j + W.residual c j) := by
    have := mul_le_mul_of_nonneg_left hPc hγ
    simp only [ConsistentSubmodular.WindowInstance.credit] at hK
    linarith
  have hs := ConsistentSubmodular.suffix_bound (lam := W.arrivalValue j) (W.residual_nonneg c j)
    (le_max_left _ _) (le_max_right _ _) hγ (by linarith) hpremise
  have h2 : 2 + (4 * β - 2) = 4 * β := by ring
  rw [h2, ← W.benchmark_eq j] at hs
  exact ConsistentSubmodular.le_of_suffix_ratio (by linarith) hα (W.benchmark_nonneg j) hs

end
