-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_tieF_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:06.076482+00:00
-- url     : https://prove2.me/submissions/98865bc5-798e-4eb0-87b0-bbd41a967332

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_tieF

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
namespace Formalism.GM.ProjS
theorem _root_.solution {s r : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (w e : Fin r → σ)
    (hmix : ∀ c, ((∃ d, t d = w c) ∧ ∀ d, t d ≠ e c) ∨ ((∀ d, t d ≠ w c) ∧ ∃ d, t d = e c))
    (g : MvPolynomial σ k) (α : k) (hg : eulL t g = α • g) (l : ℕ) :
    eulL t ((tieF w e ^ l) g) = (α - l) • (tieF w e ^ l) g := by
  induction l with
  | zero => simpa using hg
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply, eulL_tieF t ht w e hmix, ih, map_smul, Nat.cast_succ,
      sub_add_eq_sub_sub, sub_smul (α - (l : k)) 1, one_smul]
end Formalism.GM.ProjS
