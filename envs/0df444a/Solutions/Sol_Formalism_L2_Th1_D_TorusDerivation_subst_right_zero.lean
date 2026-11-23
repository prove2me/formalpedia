-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_right_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:51.627236+00:00
-- url     : https://prove2.me/submissions/4f221136-007d-4e77-b840-3fd58df0e276

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_pair

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
theorem _root_.solution {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {A : MvPowerSeries τ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.subst ![A, 0] G = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst (hasSubst_pair hA (map_zero _)), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases h : m 1 = 0
  · rw [hG m (Or.inr h), zero_smul]
  · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [zero_pow h]
end Formalism.L2.Th1.D.TorusDerivation
