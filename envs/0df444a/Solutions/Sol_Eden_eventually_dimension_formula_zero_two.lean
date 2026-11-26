-- Prove2me | solution 1 for Eden.eventually_dimension_formula_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:50.173516+00:00
-- url     : https://prove2.me/submissions/f84dcd5e-9935-4acb-a988-e2c6429a1526

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_normalized_first_nonneg_of_radius
import Theorems.Thm_Eden_eventually_dimension_formula_of_neutral_prefix
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_lyapunovExponent_eq_of_limiting_radii
import Theorems.Thm_Eden_one_lt_of_limitingSquaredRadius_eq_two
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
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
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)) :
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 := by
  have ha := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_two hc)
  have hfinite : ∀ᶠ t in atTop, ∀ i : Fin 5, i.val < 1 →
      0 ≤ normalizedLogSingularValues c t p i := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht i hi
    have hi₀ : i = 0 := Fin.ext (by omega)
    subst i
    apply normalized_first_nonneg_of_radius c ht hp
    rcases hpair with h | h
    · exact Or.inr (one_lt_of_limitingSquaredRadius_eq_two h.2).le
    · exact Or.inl (one_lt_of_limitingSquaredRadius_eq_two h.1).le
  have he := eventually_dimension_formula_of_neutral_prefix c p (k := 1) (by omega)
    (by intro i hi; rw [ha]; have : i = 0 := Fin.ext (by omega); subst i; norm_num)
    (by rw [ha]; norm_num) hfinite
  filter_upwards [he] with t ht
  exact ⟨ht.1 0 (by norm_num), ht.2.1, ht.2.2.1, by simpa using ht.2.2.2⟩
end Eden
