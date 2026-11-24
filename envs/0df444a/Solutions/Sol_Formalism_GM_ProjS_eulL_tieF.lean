-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_tieF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:08.3298+00:00
-- url     : https://prove2.me/submissions/8e2b229e-988d-4b1f-ba86-63d44eb0434d

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_pair
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1


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
    (g : MvPolynomial σ k) :
    eulL t (tieF w e g) = tieF w e (eulL t g) - tieF w e g := by
  simp only [Formalism.GM.tieF_apply', map_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun c _ => eulL_pderiv_pair t ht (w c) (e c) (hmix c) g)
end Formalism.GM.ProjS
