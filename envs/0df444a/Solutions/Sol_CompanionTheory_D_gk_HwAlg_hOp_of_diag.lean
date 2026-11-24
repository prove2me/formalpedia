-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.hOp_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:52.334357+00:00
-- url     : https://prove2.me/submissions/4fd8604d-92ff-45f1-b299-d31d57328e9b

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
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
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution {x : U} {μ : Fin n → ℂ} (hx : ∀ c, F c c x = μ c • x) : hOp F x = hgt μ • x := by
  simp only [hOp, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, hgt, Finset.sum_smul]
end CompanionTheory.D.gk.HwAlg
