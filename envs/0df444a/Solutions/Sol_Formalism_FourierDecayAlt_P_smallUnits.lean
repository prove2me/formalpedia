-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.smallUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:41.464793+00:00
-- url     : https://prove2.me/submissions/cde692fb-7552-45e9-a525-825f70cd2357

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.SmallUnits := by
  intro K _ _ _ R ψ hD hQ V hV
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  obtain ⟨m, hm⟩ := small hD hQ hpq hp hex hV
  refine ⟨ϖ ^ m, hm _ ?_⟩
  rw [Units.val_pow_eq_pow_val, mul_comm, pow_mul_pow_one hpq]
  exact R.one_mem
end Formalism.FourierDecayAlt.P
