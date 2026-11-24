-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:23.218061+00:00
-- url     : https://prove2.me/submissions/52feb606-bc91-4caf-9919-d2088dfb2a4f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrs_secondCountable_abs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology
open scoped Pointwise
open Formalism.MainNotions.S
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    SecondCountableTopology I.Gf := by
  obtain ⟨U, hU, h1, hb⟩ : ∃ U : ℕ → Set I.Gf, (∀ n, IsOpen (U n)) ∧ (∀ n, (1 : I.Gf) ∈ U n) ∧
      ∀ O ∈ 𝓝 (1 : I.Gf), ∃ n, U n ⊆ O := by
    refine ⟨_, fun n => I.topf_open (n + 1) (by omega), ?_, ?_⟩
    · intro n
      refine ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
      simp
    · intro O hO
      obtain ⟨g, hg, hsub⟩ := I.topf_basis O hO
      refine ⟨g - 1, ?_⟩
      simp only [Nat.sub_add_cancel hg]
      exact hsub
  exact rrs_secondCountable_abs μf U hU h1 hb
end Formalism.MainNotions.LeviCoordinates
