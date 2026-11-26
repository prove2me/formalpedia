-- Prove2me | solution 1 for Eden.frequency_solution_unique_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:36.892591+00:00
-- url     : https://prove2.me/submissions/db54eff0-cf98-4431-9909-ab40caff0f5f

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_contDiff_frequencyVectorField
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
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
theorem _root_.solution (c ν : ℝ) {a b : ℝ} {f g : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (frequencyVectorField c ν (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (frequencyVectorField c ν (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hc : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨K, hK⟩ := (contDiff_frequencyVectorField c ν 1).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall (0 : PhaseSpace) R) (isCompact_closedBall 0 R)
  have hfs : ∀ t ∈ Ico a b, f t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR (f t) (Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
  have hgs : ∀ t ∈ Ico a b, g t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR (g t) (Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => frequencyVectorField c ν) (s := fun _ => Metric.closedBall 0 R)
    (K := K) (fun _ _ => hK) hf hf' hfs hg hg' hgs ha
end Eden
