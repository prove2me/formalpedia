-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_e_S_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:51.18686+00:00
-- url     : https://prove2.me/submissions/4728c5b5-3156-4950-b4d8-b14b39ac2552

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_eulL_mul
import Theorems.Thm_Formalism_GM_pderiv_e_S


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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (β : k) (hE : eulL e g = β • g) :
    eulL e ((∑ d, X (w d) * X (e d)) * g) = (β + 1) • ((∑ d, X (w d) * X (e d)) * g) := by
  have hR : eulL e (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d) := by
    rw [eulL_apply]
    exact Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_e_S he hwe c, mul_comm])
  rw [eulL_mul, hR, hE, mul_smul_comm, add_smul, one_smul]
  abel
end Formalism.GM.ProjS
