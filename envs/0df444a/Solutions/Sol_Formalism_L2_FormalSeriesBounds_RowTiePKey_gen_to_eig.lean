-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePKey.gen_to_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:09.357378+00:00
-- url     : https://prove2.me/submissions/b91fa8ff-6cde-418a-a31e-5f212340afc0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJointDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJoint
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePKey_sq_to_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePKey
variable {C : Type} [Field C] [CharZero C] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePKey
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (w : Fin n → C)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' t : Module.End C (Fin n → C)) μ) : Matrix.mulVec t w = μ • w := by
  rw [Module.End.mem_maxGenEigenspace] at hw
  obtain ⟨k, hk⟩ := hw
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    subst hk
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hk
    have hy := ih _ hk
    have e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w := by
      simp [Matrix.toLin'_apply]
    rw [e] at hy
    exact sq_to_eig hq t ht μ w hy
end Formalism.L2.FormalSeriesBounds.RowTiePKey
