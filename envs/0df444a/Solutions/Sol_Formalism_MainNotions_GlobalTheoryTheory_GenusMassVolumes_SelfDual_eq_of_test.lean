-- Prove2me | solution 1 for Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual.eq_of_test
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:27.018741+00:00
-- url     : https://prove2.me/submissions/d94d86fd-9647-4655-8cbc-84fc22e1c447

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace SelfDual
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ)
    (z : V) (hz : Φ (-z) ≠ 0) : ν = μ := by
  have := hμ.1
  have := hν.1
  have e : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  set c : NNReal := Measure.addHaarScalarFactor ν μ with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂ν = (c : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have h1 := hμ.2 Φ hc hs hI z
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂ν) ν := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hν.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]
end SelfDual
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
