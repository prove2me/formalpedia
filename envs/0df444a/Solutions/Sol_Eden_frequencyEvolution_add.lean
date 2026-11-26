-- Prove2me | solution 1 for Eden.frequencyEvolution_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:39.353219+00:00
-- url     : https://prove2.me/submissions/c28ba240-865a-4d8d-9801-8940b6c70932

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
import Theorems.Thm_Eden_frequencyEvolution_unique
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_frequencyEvolution
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
attribute [local simp] Eden.frequencyEvolution_zero_time
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
theorem _root_.solution (c ν : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    frequencyEvolution c ν (s + t) p = frequencyEvolution c ν t (frequencyEvolution c ν s p) := by
  have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => frequencyEvolution c ν (s + u) p)
      (frequencyVectorField c ν (frequencyEvolution c ν (s + τ) p)) τ := by
    intro τ hτ
    have h := (hasDerivAt_frequencyEvolution c ν (add_nonneg hs hτ) p).scomp τ
      ((hasDerivAt_id τ).const_add s)
    simpa only [Function.comp_def, one_smul] using h
  exact frequencyEvolution_unique c ν (frequencyEvolution c ν s p)
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd τ hτ).hasDerivWithinAt) (by simp) ht
end Eden
