-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.exists_last_eligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:21.231206+00:00
-- url     : https://prove2.me/submissions/c8621bd9-9f8b-419b-80e0-a6848f0436d7

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

theorem solution {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ c : Fin (W.lastStage + 1), W.envelope β ≤ W.credit c ∧
      ∀ j, c < j → W.credit j < W.envelope β := by
  classical
  obtain ⟨h, -, hhK⟩ := W.exists_envelope_eligible hβ'
  let E : Finset (Fin (W.lastStage + 1)) :=
    Finset.univ.filter (fun j => W.envelope β ≤ W.credit j)
  have hhE : h ∈ E := by simpa [E] using hhK
  refine ⟨E.max' ⟨h, hhE⟩, (Finset.mem_filter.mp (E.max'_mem ⟨h, hhE⟩)).2, ?_⟩
  intro j hcj
  by_contra hn
  have hjE : j ∈ E := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_of_not_gt hn
  exact absurd (E.le_max' j hjE) (not_le.mpr hcj)

end
