-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.self_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:35.262529+00:00
-- url     : https://prove2.me/submissions/e4bf9cea-2c69-4b50-b1aa-ebd0d3837ef2

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons

set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (F : Fin n → Fin n → Module.End ℂ U) (w : U) : w ∈ lowSpan F w := by
  simpa using word_mem F w (l := []) (by simp [Lower])
end CompanionTheory.D.gk.HwAlg
