-- Prove2me | solution 1 for Formalism.GM.FockB.free_of_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:45.372085+00:00
-- url     : https://prove2.me/submissions/76c88c1e-6b2f-4eb6-9608-bafb39aa9874

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] {v : σ} {y : MvPolynomial σ k} (h : pderiv v y = 0) :
    ∀ m ∈ y.support, m v = 0 := by
  classical
  intro m hm
  by_contra hne
  have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne)
  have hc := congrArg (coeff (m - Finsupp.single v 1)) h
  rw [coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero] at hc
  have h1 : ((((m - Finsupp.single v 1 : σ →₀ ℕ)) v : ℕ) : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  exact (mem_support_iff.mp hm) ((mul_eq_zero.mp hc).resolve_right h1)
end Formalism.GM.FockB
