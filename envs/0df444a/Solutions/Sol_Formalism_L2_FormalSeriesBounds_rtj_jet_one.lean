-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_jet_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:56.55868+00:00
-- url     : https://prove2.me/submissions/cd780a76-f877-42c5-ac48-263f92b5af37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_subset

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : jetAt0 (1 : MvPolynomial σ K) (1 : MvPowerSeries σ K) = 1 := by
  have hs : (1 : MvPolynomial σ K).support ⊆ {0} := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  rw [rtj_jet_subset 1 1 {0} hs]
  simp [mfact]
end Formalism.L2.FormalSeriesBounds
