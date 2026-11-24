-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_zero_of_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:12.281421+00:00
-- url     : https://prove2.me/submissions/4919e813-5626-4b9a-b979-becf02eeda52

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {κ : Type} (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries κ K) f = 0 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : PowerSeries.coeff 0 f = 0 := by simpa using hf
    rw [this, zero_smul]
  · rw [zero_pow hm.ne', map_zero, smul_zero]
end Formalism.L2.Th1.D.TorusDerivation
