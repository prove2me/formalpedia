-- Prove2me | solution 1 for Formalism.GM.ProjS.F_S_mul_k
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:43.79187+00:00
-- url     : https://prove2.me/submissions/04ae2d01-19b0-4588-853f-fbe3685cfb76

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_pderiv_e_S
import Theorems.Thm_Formalism_GM_pderiv_w_S
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
variable {s : ℕ} {w e : Fin s → σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) :
    tieF w e ((∑ d, X (w d) * X (e d)) * g) =
      (∑ d, X (w d) * X (e d)) * tieF w e g + (α + β + s) • g := by
  have hc : ∀ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) =
      g + X (w c) * pderiv (w c) g + X (e c) * pderiv (e c) g +
        (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g) := by
    intro c
    rw [MvPolynomial.pderiv_mul, Formalism.GM.pderiv_e_S he hwe c, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, Formalism.GM.pderiv_w_S hw hwe c]
    ring
  rw [Formalism.GM.tieF_apply', Formalism.GM.tieF_apply', Finset.sum_congr rfl (fun c _ => hc c)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  rw [← eulL_apply w g, ← eulL_apply e g, hW, hE]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_natCast, nsmul_eq_mul]
  ring
end Formalism.GM.ProjS
