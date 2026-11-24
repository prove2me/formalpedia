-- Prove2me | solution 1 for Formalism.GM.ProjS.pderiv_sv_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:10.744806+00:00
-- url     : https://prove2.me/submissions/1b121473-a980-4b39-a80e-4e8f738a7c62

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_pderiv_of_free
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
private theorem mvPolynomial_pderiv_X_eq_zero_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  classical
  rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg h]
private theorem pderiv_X_pow_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) : pderiv i (X j ^ z : MvPolynomial σ k) = 0 := by
  rw [Derivation.leibniz_pow, mvPolynomial_pderiv_X_eq_zero_of_ne h, smul_zero, smul_zero]
private theorem pderiv_X_pow_mul_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) (g : MvPolynomial σ k) :
    pderiv i (X j ^ z * g) = X j ^ z * pderiv i g := by
  rw [MvPolynomial.pderiv_mul, pderiv_X_pow_of_ne h, zero_mul, zero_add]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
section
variable {s : ℕ} {w e : Fin s → σ}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
section
variable {o n z : ℕ} {y : MvPolynomial σ k}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
variable {o n z : ℕ} {y : MvPolynomial σ k}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) :
    pderiv sv (X zv ^ z * y) = 0 := by
  rw [pderiv_X_pow_mul_of_ne hv.2.2.2.2 z y, pderiv_of_free sv y (fun m hm => (hz m hm).2), mul_zero]
end Formalism.GM.ProjS
