-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.diag_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:11.047542+00:00
-- url     : https://prove2.me/submissions/3abafa53-14ea-4365-a5fa-a5be2ae3aeb5

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_comm_apply
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
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)) (c : Fin n), F c c (word F l w) = wt ν l c • word F l w := by
  intro l
  induction l with
  | nil => intro c; simpa [wt] using hw.1 c
  | cons p l ih =>
    intro c
    rw [word_cons, Module.End.mul_apply, comm_apply hF, ih, map_smul]
    simp only [wt, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c
    · subst h1; rw [h2] at *; simp
    · subst h1; simp [h2, Ne.symm h2, add_smul]
    · subst h2; simp [h1, add_smul, sub_eq_add_neg]
    · simp [h1, h2, Ne.symm h2]
end CompanionTheory.D.gk.HwAlg
