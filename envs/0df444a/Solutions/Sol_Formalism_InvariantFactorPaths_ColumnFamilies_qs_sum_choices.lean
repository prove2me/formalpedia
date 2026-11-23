-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_choices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:09.636078+00:00
-- url     : https://prove2.me/submissions/75607b73-d97e-476c-a4e8-c2a000aa2c70

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_prod_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (S D : Finset ℤ) (hD : D ⊆ S) (u : ℤ → R) (p : ↥D → Fin n → Prop) [∀ c x, Decidable (p c x)]
    (s w : ↥D → Fin n → R) (F : (↥D → Fin n) → ℤ → R)
    (hF1 : ∀ m, ∀ c ∈ S \ D, F m c = u c) (hF2 : ∀ m (c : ↥D), F m c.1 = w c (m c))
    (v : ↥D → Fin n → R) :
    ∑ m : ↥D → Fin n, (if ∀ c, p c (m c) then (∏ c, s c (m c)) * (∏ c ∈ S, F m c) * ∏ c, v c (m c) else 0) =
      (∏ c ∈ S \ D, u c) * ∏ c : ↥D, ∑ x, if p c x then s c x * w c x * v c x else 0 := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.prod_ite_zero]
  split_ifs with h
  · rw [qs_prod_split S D hD, Finset.prod_congr rfl (hF1 m), Finset.prod_congr rfl (fun c _ => hF2 m c),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
