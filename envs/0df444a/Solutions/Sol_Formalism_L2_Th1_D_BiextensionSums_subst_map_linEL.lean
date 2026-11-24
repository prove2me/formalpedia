-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionSums.subst_map_linEL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:59:16.939797+00:00
-- url     : https://prove2.me/submissions/123a0854-135e-41d2-8b1f-7d486d677656

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_entLog
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211
import Theorems.Thm_P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums
namespace Formalism.L2.Th1.D.BiextensionSums
theorem _root_.solution {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linEL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then C (j (σ^[s.val] c)) * X (s, a, b) else 0 := by
  unfold linEL
  rw [map_sum, subst_sum hg]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [map_mul, map_C, Formalism.DworkPowerSeriesWeights.Transfer.map_entLog, subst_mul hg, subst_C, hgE]
  · rw [map_zero, subst_zero' hg]
end Formalism.L2.Th1.D.BiextensionSums
