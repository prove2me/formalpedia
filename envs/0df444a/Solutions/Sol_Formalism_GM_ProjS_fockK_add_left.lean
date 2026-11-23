-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:29.262224+00:00
-- url     : https://prove2.me/submissions/65d9f83e-29ba-4fc8-bbdc-22733c4047f1

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_superset
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
private theorem mvPolynomial_coeff_eq_zero_of_not_mem_support {p : MvPolynomial σ k} {m : σ →₀ ℕ} (h : m ∉ p.support) :
    coeff m p = 0 := by
  simpa [MvPolynomial.mem_support_iff] using h
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
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (F F' G : MvPolynomial σ k) :
    M.fockK (F + F') G = M.fockK F G + M.fockK F' G := by
  classical
  have h1 : (F + F').support ⊆ F.support ∪ F'.support := by
    intro m hm
    rw [Finset.mem_union]
    by_contra h
    rw [not_or] at h
    apply (MvPolynomial.mem_support_iff.mp hm)
    rw [MvPolynomial.coeff_add, mvPolynomial_coeff_eq_zero_of_not_mem_support h.1, mvPolynomial_coeff_eq_zero_of_not_mem_support h.2, add_zero]
  rw [fockK_superset _ G _ h1,
    fockK_superset F G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_left _ hx),
    fockK_superset F' G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring
end Formalism.GM.ProjS
