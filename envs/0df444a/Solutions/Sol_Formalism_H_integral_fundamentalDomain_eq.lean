-- Prove2me | solution 1 for Formalism.H.integral_fundamentalDomain_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:18.969862+00:00
-- url     : https://prove2.me/submissions/119cb695-cf74-4fb3-9929-a161871ec0a5

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Theorems.Thm_Formalism_H_volume_boxIco
import Theorems.Thm_Formalism_H_fundamentalDomain_eq_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]
namespace Formalism.H
theorem _root_.solution (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by
  let ψ : V ≃ᵐ (ι → ℝ) := e.equivFunL.toHomeomorph.toMeasurableEquiv
  have hψ : (ψ : V → ι → ℝ) = e.equivFunL := rfl
  set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef
  haveI : ν.IsAddHaarMeasure := by
    rw [hνdef, hψ]; exact e.equivFunL.isAddHaarMeasure_map volume
  have hν : ν = ν.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e) := by
    rw [hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]
  have hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e) := by
    rw [← hbox]
    conv_rhs => rw [hν]
    simp [volume_boxIco]
  have hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν := by
    rw [hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]
    simp only [hψ, ContinuousLinearEquiv.symm_apply_apply]
  rw [hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc,
    ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]
end Formalism.H
