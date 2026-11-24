-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:44.207039+00:00
-- url     : https://prove2.me/submissions/7883a710-9c5d-4c32-aa21-3288cf1d539a

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support

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
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (zv : σ) (z a : ℕ) (ha : ∑ c, (Finsupp.single zv z) (t c) = a) :
    eulL t (X zv ^ z : MvPolynomial σ k) = (a : k) • X zv ^ z := by
  classical
  apply eulL_of_support
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_pow] at hm
  split_ifs at hm with h
  · rw [← h]; exact ha
  · exact absurd rfl hm
end Formalism.GM.ProjS
