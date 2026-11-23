-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:51.618799+00:00
-- url     : https://prove2.me/submissions/6848bc70-1a5d-4f14-bd8b-f4552e46c643

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
    {B : MvPowerSeries τ K} (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![0, B] G = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst (hasSubst_pair (map_zero _) hB), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases h : m 0 = 0
  · rw [hG m (Or.inl h), zero_smul]
  · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [zero_pow h]
end Formalism.L2.Th1.D.TorusDerivation
