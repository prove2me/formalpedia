-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.lu_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.788876+00:00
-- url     : https://prove2.me/submissions/a80d738a-71aa-45ed-a4e9-3994f1993dd6

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution (h u : Matrix (Fin n) (Fin n) K) (hh : IsLowUni h) (hu : IsUpUni u)
    (i j : Fin n) :
    (h * u) i j = (∑ k, if k < i ∧ k < j then h i k * u k j else 0) + (h + u - 1) i j := by
  have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
  have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
  have key : ∀ k, h i k * u k j = (if k < i ∧ k < j then h i k * u k j else 0) +
      (if k = min i j then (h + u - 1) i j else 0) := by
    intro k
    rcases lt_trichotomy k (min i j) with hk | hk | hk
    · rw [if_pos (lt_min_iff.mp hk), if_neg hk.ne, add_zero]
    · have hn : ¬ (k < i ∧ k < j) := fun hk' => (lt_min hk'.1 hk'.2).ne hk
      rw [if_neg hn, if_pos hk, zero_add, hk]
      simp only [Matrix.sub_apply, Matrix.add_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [min_eq_left hij.le, hh.2, hL i j hij, Matrix.one_apply_ne hij.ne]; ring
      · rw [min_self, hh.2, hu.2, Matrix.one_apply_eq]; ring
      · rw [min_eq_right hij.le, hu.2, hU i j hij, Matrix.one_apply_ne hij.ne']; ring
    · have hn : ¬ (k < i ∧ k < j) := fun hk' => lt_asymm (lt_min hk'.1 hk'.2) hk
      rw [if_neg hn, if_neg hk.ne', add_zero]
      rcases min_lt_iff.mp hk with hik | hjk
      · rw [hL i k hik, zero_mul]
      · rw [hU k j hjk, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.DoubleCosetMeasures.P.Supp
