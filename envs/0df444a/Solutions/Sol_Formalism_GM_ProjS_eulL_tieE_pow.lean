-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_tieE_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:52.877086+00:00
-- url     : https://prove2.me/submissions/de2de6a2-0d5b-4fee-aaa2-43321b4cfdbe

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_w_S_mul
import Theorems.Thm_Formalism_GM_ProjS_eulL_e_S_mul
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
variable {s : ℕ} {w e : Fin s → σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) (j : ℕ) :
    eulL w ((tieE w e ^ j) g) = (α + j) • (tieE w e ^ j) g ∧
    eulL e ((tieE w e ^ j) g) = (β + j) • (tieE w e ^ j) g := by
  induction j with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]
    exact ⟨hW, hE⟩
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, Formalism.GM.tieE_apply', Nat.cast_succ, ← add_assoc, ← add_assoc]
    exact ⟨eulL_w_S_mul hw hwe _ _ ih.1, eulL_e_S_mul he hwe _ _ ih.2⟩
end Formalism.GM.ProjS
