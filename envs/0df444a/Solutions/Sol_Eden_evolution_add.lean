-- Prove2me | solution 1 for Eden.evolution_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:11.007472+00:00
-- url     : https://prove2.me/submissions/ac6a3d8c-964f-470d-95fc-fac5f6131083

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
import Theorems.Thm_Eden_evolution_unique
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
theorem _root_.solution (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    evolution c (s + t) p = evolution c t (evolution c s p) := by
  have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => evolution c (s + u) p)
      (vectorField c (evolution c (s + τ) p)) τ := by
    intro τ hτ
    have h := (hasDerivAt_evolution c (add_nonneg hs hτ) p).scomp τ
      ((hasDerivAt_id τ).const_add s)
    simpa only [Function.comp_def, one_smul] using h
  exact evolution_unique c (evolution c s p)
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd τ hτ).hasDerivWithinAt) (by simp) ht
end Eden
