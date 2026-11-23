-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.ae_cof_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:59.442952+00:00
-- url     : https://prove2.me/submissions/4671cd27-0cfc-419d-a18d-6c9b695cea5e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_cof_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (β t : ℂ) (ht : t ≠ 0) {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hX : IsStrictUpper X) : ∀ᵐ B ∂(muPi β (Fin (m + 1))), Cof X B t ≠ 0 := by
  rw [muPi_eq]
  refine Measure.ae_smul_measure ?_ _
  have hker : LinearMap.ker (cofLin X t) ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ LinearMap.ker (cofLin X t) := by rw [h]; trivial
    rw [LinearMap.mem_ker] at h1
    exact pow_ne_zero m ht ((cof_single X hX t).symm.trans h1)
  have h2 := Measure.addHaar_submodule (volume : Measure (Fin (m + 1) → ℂ)) _ hker
  exact (measure_eq_zero_iff_ae_notMem.1 h2).mono fun B hB h => hB (LinearMap.mem_ker.2 h)
end Formalism.FourierDecayAlt.P.G7
