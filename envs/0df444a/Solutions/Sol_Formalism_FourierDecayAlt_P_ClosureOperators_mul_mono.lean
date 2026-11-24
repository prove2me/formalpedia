-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:54.302905+00:00
-- url     : https://prove2.me/submissions/061237a0-2b4a-4f64-8427-416693f7ca98

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mono_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), (∀ a b, f a * f b = f b * f a) →
    ∀ (a : Fin n → ℕ) (x : Fin n), ∃ a' : Fin n → ℕ, f x * mono f a = mono f a' := by
  intro n
  induction n with
  | zero => intro f _ a x; exact x.elim0
  | succ k ih =>
    intro f hf a x
    cases x using Fin.cases with
    | zero =>
      refine ⟨Fin.cons (a 0 + 1) (fun y => a y.succ), ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [pow_succ', mul_assoc]
    | succ y =>
      obtain ⟨a'', h''⟩ := ih (fun z => f z.succ) (fun p q => hf _ _) (fun z => a z.succ) y
      refine ⟨Fin.cons (a 0) a'', ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← mul_assoc, ((show Commute (f y.succ) (f 0) from hf _ _).pow_right (a 0)).eq, mul_assoc, h'']
end Formalism.FourierDecayAlt.P.ClosureOperators
