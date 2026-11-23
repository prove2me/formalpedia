-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_w_S_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:29.598847+00:00
-- url     : https://prove2.me/submissions/15c560aa-fa46-4ee2-8c22-8e3ff6fb20ed

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_eulL_mul
import Theorems.Thm_Formalism_GM_pderiv_w_S


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
theorem _root_.solution (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α : k) (hW : eulL w g = α • g) :
    eulL w ((∑ d, X (w d) * X (e d)) * g) = (α + 1) • ((∑ d, X (w d) * X (e d)) * g) := by
  have hR : eulL w (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d) := by
    rw [eulL_apply]
    exact Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_w_S hw hwe c])
  rw [eulL_mul, hR, hW, mul_smul_comm, add_smul, one_smul]
  abel
end Formalism.GM.ProjS
