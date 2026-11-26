-- Prove2me | solution 1 for Eden.evolution_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:39.393596+00:00
-- url     : https://prove2.me/submissions/4fffe017-e3ce-4ad6-8068-4b793f43c715

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
import Theorems.Thm_Eden_solution_unique_on_Icc
import Theorems.Thm_Eden_continuousOn_evolution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_evolution
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) {f : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Ici 0))
    (hf' : ∀ t, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t)
    (h0 : f 0 = p) : EqOn f (fun t => evolution c t p) (Ici 0) := by
  intro t ht
  have hu := solution_unique_on_Icc c (a := 0) (b := t)
    (hf.mono Icc_subset_Ici_self) (fun τ hτ => hf' τ hτ.1)
    ((continuousOn_evolution c p).mono Icc_subset_Ici_self)
    (fun τ hτ => (hasDerivAt_evolution c hτ.1 p).hasDerivWithinAt)
    (by simpa using h0)
  exact hu ⟨ht, le_rfl⟩
end Eden
