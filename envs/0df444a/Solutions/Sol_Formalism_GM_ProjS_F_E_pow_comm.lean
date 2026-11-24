-- Prove2me | solution 1 for Formalism.GM.ProjS.F_E_pow_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.414805+00:00
-- url     : https://prove2.me/submissions/a4becda2-1ec2-4d83-881a-c6972b15e670

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_tieE_pow
import Theorems.Thm_Formalism_GM_ProjS_F_S_mul_k
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
    tieF w e ((tieE w e ^ (j + 1)) g) =
      (tieE w e ^ (j + 1)) (tieF w e g) + (((j : k) + 1) * (α + β + s + j)) • (tieE w e ^ j) g := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Formalism.GM.tieE_apply', Nat.cast_zero, one_mul, add_zero]
    exact F_S_mul_k hw he hwe g α β hW hE
  | succ j ih =>
    have hr := eulL_tieE_pow hw he hwe g α β hW hE (j + 1)
    have e1 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1 + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ (j + 1)) x := by
      intro x
      rw [pow_succ' (Formalism.GM.tieE (k := k) w e) (j + 1), Module.End.mul_apply, Formalism.GM.tieE_apply']
    have e0 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ j) x := by
      intro x
      rw [pow_succ' (Formalism.GM.tieE (k := k) w e) j, Module.End.mul_apply, Formalism.GM.tieE_apply']
    have hcoef : ((j : k) + 1) * (α + β + s + j) + (α + ((j + 1 : ℕ) : k) + (β + ((j + 1 : ℕ) : k)) + s) =
        (((j + 1 : ℕ) : k) + 1) * (α + β + s + ((j + 1 : ℕ) : k)) := by
      push_cast
      ring
    rw [e1, e1, F_S_mul_k hw he hwe _ _ _ hr.1 hr.2, ih, mul_add, mul_smul_comm, ← e0,
      add_assoc, ← add_smul, hcoef]
end Formalism.GM.ProjS
