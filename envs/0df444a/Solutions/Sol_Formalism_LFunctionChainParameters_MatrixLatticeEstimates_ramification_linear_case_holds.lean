-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.ramification_linear_case_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:47.368227+00:00
-- url     : https://prove2.me/submissions/24947094-8deb-43cd-8e42-0cffd99f4be8

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_input_size_transfer_holds
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_ramification_transfer_holds
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_first_family_transfer_holds
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_second_family_transfer_holds
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressDiagDefectBound
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressTraceSquareBound


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
theorem _root_.solution : RamLin := by
  intro I α _ _ ιf ι _ _ _ _ Bf Vr ga Dstar sg η0 η1 e0 de hV hga hD hsg hsg20 hR h0 h0' h1 he0 hse
    hde hde4 hcor hS
  have hS' := (input_size_transfer_holds I α ιf Bf ga Dstar η0 η1 e0).2 hS
  obtain ⟨hB, hI⟩ := ramification_transfer_holds I α ιf ι Bf Vr
  have hV' := hI.2 hV
  have f1 := HilbertSchmidtNormSquare.compressTraceSquareBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga Dstar sg η0 η1 e0 de hV' hga hD hsg hsg20
    hR h0 h0' h1 he0 hse hde hde4 hcor hS'
  obtain ⟨hRr, f2⟩ := HilbertSchmidtNormSquare.compressDiagDefectBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga de e0 hV' (by linarith) he0 hS'.2.1 hcor
  rw [← hB] at f1 f2
  refine ⟨(first_family_transfer_holds I α ι _ ga _).1 f1, (second_family_transfer_holds I α ι _ ga _ hga).1 f2, ?_, ?_⟩
  · have hs := Real.sq_sqrt he0
    have hn := Real.sqrt_nonneg e0
    nlinarith
  · have hpos : (0 : ℝ) < RsG ιf := lt_of_lt_of_le (div_pos hD hsg) hR
    have hpos' : (0 : ℝ) < HilbertSchmidtNormSquare.Rs (fun i => Fintype.card (ι i)) := by
      refine lt_of_lt_of_le ?_ hRr
      exact mul_pos (by linarith) hpos
    unfold HilbertSchmidtNormSquare.Rs at hpos'
    exact_mod_cast hpos'
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
