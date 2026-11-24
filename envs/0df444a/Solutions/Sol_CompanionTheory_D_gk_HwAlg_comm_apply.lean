-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:38.720244+00:00
-- url     : https://prove2.me/submissions/73fe7c43-f227-4fc8-a660-72913584f3dd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

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
theorem _root_.solution {F : Fin n → Fin n → Module.End ℂ U} (hF : GlRel F) (i j a b : Fin n) (u : U) :
    F i j (F a b u) = F a b (F i j u) +
      ((if j = a then F i b u else 0) - (if b = i then F a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ U => T u) (hF i j a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]
end CompanionTheory.D.gk.HwAlg
