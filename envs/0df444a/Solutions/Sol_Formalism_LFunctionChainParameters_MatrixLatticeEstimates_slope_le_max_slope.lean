-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.slope_le_max_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:34.866448+00:00
-- url     : https://prove2.me/submissions/18cef8da-422a-404a-a6ec-699fb9bb64ce

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_HN_muChar
import Theorems.Thm_Formalism_HN_plLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ w, IsUnit (X w).det) (N : Submodule (𝓞 K) V) (hFG : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) (hc : 0 < Fintype.card ι) :
    muDef b X N ≤ muMaxDef b X N := by
  have hne : N ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Submodule K V) = ⊤ := by rw [← hsp]; simp
    have : Subsingleton (Submodule K V) := subsingleton_of_bot_eq_top h0
    have : Subsingleton V := (Submodule.subsingleton_iff K).1 inferInstance
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  have hLat := (plLat K V ι b X hX N hFG).1
  have := (muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) N hLat hne).2.2.2.2
  unfold muDef muMaxDef
  linarith
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
