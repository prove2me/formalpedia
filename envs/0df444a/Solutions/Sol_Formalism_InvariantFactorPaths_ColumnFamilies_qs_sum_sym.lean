-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:25.537795+00:00
-- url     : https://prove2.me/submissions/41ebe712-5348-491a-991f-21374a675bd3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sym_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) {b : ℕ}
    (hb : Fintype.card ι = b) (m : ι → Fin n) (α : SymIdx n b) (r : A) :
    ∑ β : SymIdx n b, qs_SM G b α β * (if (∀ x, qs_cnt m x = (β.1 x : ℕ)) then r else 0) =
      (∑ a : ι → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then ∏ c, G (a c) (m c) else 0) * r := by
  classical
  rw [Finset.sum_eq_single (qs_mon hb m)]
  · have h0 : ∀ x, qs_cnt m x = ((qs_mon hb m).1 x : ℕ) := fun x => rfl
    rw [if_pos h0]
    congr 1
    exact qs_sym_mul G m _ h0 (symMono α)
  · intro β _ hβ
    rw [if_neg, mul_zero]
    intro h
    exact hβ (Subtype.ext (funext fun x => Fin.ext (h x).symm))
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.ColumnFamilies
