-- Prove2me | solution 1 for ConsistentSubmodular.mixtureComparisons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:36.772413+00:00
-- url     : https://prove2.me/submissions/2dd40824-fc37-4ebd-8b30-e9129e8aea59

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero
import Theorems.Thm_ConsistentSubmodular_physical_multilinear_lift
import Theorems.Thm_ConsistentSubmodular_WindowInstance_bufferMixtureValue_le_average

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem finiteExpectation_eq_sampleExpectation [Fintype ι] (p : ι → ℝ) (U : Finset ι)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    finiteExpectation p v = sampleExpectation U p v := by
  rw [← sampleExpectation_univ, sampleExpectation_inter_zero U Finset.univ p hp,
    Finset.univ_inter]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- Inequality (21): `H_Q(p) ≤ F_Q(z(p))` on the type cube with mass at most
one. The lift `physical_multilinear_lift` samples over all elements; `z(p)`
vanishes off `V_now`, so the multilinear extension over `V_now` is the same. -/
theorem bufferMixtureValue_le_multilinearExtension (Q : Finset (Fin n)) (p : Point W.lastStage)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i ≤ 1) :
    W.bufferMixtureValue Q p ≤ W.multilinearExtension Q (W.physicalVector p) := by
  have h := physical_multilinear_lift W.objective W.candidate Q p hp hmass
  have hzero : ∀ e ∉ W.present, physicalProbability W.candidate p e = 0 := by
    intro e he
    unfold physicalProbability
    exact Finset.sum_eq_zero fun i _ => if_neg fun hi => he (W.candidate_subset i hi)
  rw [finiteExpectation_eq_sampleExpectation _ W.present hzero] at h
  exact h

end WindowInstance

namespace WindowBounds

/-- **Lemma B.2** (mixture comparisons). -/
theorem mixtureComparisons : MixtureComparisonsGoal := fun _ W Q =>
  ⟨fun p hp hmass => W.bufferMixtureValue_le_multilinearExtension Q p hp hmass,
    fun _ hp => W.bufferMixtureValue_le_average Q hp⟩

end WindowBounds

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : MixtureComparisonsGoal :=
  WindowBounds.mixtureComparisons

end
