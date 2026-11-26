-- Prove2me | solution 1 for Eden.volumeDefect_eq_integral_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:17.205066+00:00
-- url     : https://prove2.me/submissions/4762efb9-d988-4027-9135-4bb089bb5cd6

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e
import Theorems.Thm_P2M_Eden_radiusSq__evolution_ce05ee2f5645
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.radialDefect_at_one
section
noncomputable section
open Set
namespace Eden
private theorem defect_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => (squaredRadiusEvolution τ s - 1) ^ 2)
      MeasureTheory.volume 0 t := by
  have hc := (((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)).sub
      (continuousOn_const (c := (1 : ℝ)))).pow 2
  exact hc.intervalIntegrable_of_Icc ht
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) := by
  unfold volumeDefect radialDefect
  rw [← intervalIntegral.integral_add (defect_intervalIntegrable ht (radiusSq₁ p))
    (defect_intervalIntegrable ht (radiusSq₂ p))]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ₀ : 0 ≤ τ := (uIcc_of_le ht ▸ hτ).1
  dsimp only
  rw [radiusSq₁_evolution c hτ₀, radiusSq₂_evolution c hτ₀]
end Eden
