-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.coeff_beMean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:45.916447+00:00
-- url     : https://prove2.me/submissions/13e466d0-a688-4702-bbfa-a434d66de84a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_torus_coefficient

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
open TorusDerivation
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) (ζ : K) (n : ZMod d →₀ ℕ) :
    MvPowerSeries.coeff n (beMean l σ be0 om oms ζ) =
      (((l ^ d - 1 : ℕ) : K)⁻¹) * ((∑ k ∈ Finset.range (l ^ d - 1), wt l ζ n ^ k) *
        MvPowerSeries.coeff n (beTil l σ be0 om oms)) := by
  unfold beMean
  rw [MvPowerSeries.coeff_C_mul, map_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [torus_coefficient]
  congr 1
  unfold wt
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun s _ => ?_
  have e : (ζ ^ k) ^ lw l s = (ζ ^ lw l s) ^ k := by
    rw [← zpow_natCast ζ k, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  rw [e, ← pow_mul, ← pow_mul, mul_comm]
end Formalism.L2.Th1.D.TorusDerivation
