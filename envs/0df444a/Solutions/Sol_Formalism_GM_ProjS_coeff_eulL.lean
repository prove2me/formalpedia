-- Prove2me | solution 1 for Formalism.GM.ProjS.coeff_eulL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:17.563057+00:00
-- url     : https://prove2.me/submissions/cf925d9a-8117-4145-80e1-dcbd0258928f

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da


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
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (g : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (eulL t g) = coeff m g * ∑ c, (m (t c) : k) := by
  rw [eulL_apply, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => Formalism.GM.coeff_X_mul_pderiv' (t c) g m)
end Formalism.GM.ProjS
