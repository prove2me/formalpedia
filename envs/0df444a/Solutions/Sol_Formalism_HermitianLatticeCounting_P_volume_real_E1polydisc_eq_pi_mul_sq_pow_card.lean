-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volume_real_E1polydisc_eq_pi_mul_sq_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:42.537838+00:00
-- url     : https://prove2.me/submissions/a327489a-4b3e-4658-ba8b-f14e9424d2cd

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_polydisc_eq_pi_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] (ro : ℝ) (hro : 0 < ro) (D : ι → ℂ) :
    (volume : Measure (ι → ℂ)).real (CenteredPolydisc ro D) = (π * (ro / 2) ^ 2) ^ Fintype.card ι := by
  rw [polydisc_eq_pi_ball, Measure.real, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  rw [ENNReal.toReal_ofReal (by positivity), mul_comm]
end Formalism.HermitianLatticeCounting.P
