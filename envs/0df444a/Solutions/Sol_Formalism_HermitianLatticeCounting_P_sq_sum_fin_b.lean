-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sq_sum_fin_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:29.74133+00:00
-- url     : https://prove2.me/submissions/2ab227cd-e959-4da6-90e8-21444b66f193

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = ∑ x, j x ^ 2 + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
  simp only [Finset.sum_filter]
  have h1 : ∀ x y : Fin a, j x * j y = (if x < y then j x * j y else 0)
      + (if y < x then j x * j y else 0) + (if x = y then j x ^ 2 else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h; simp [sq]
    · simp [h, h.ne', h.not_gt]
  have h2 : ∑ x, ∑ y, (if y < x then j x * j y else 0) = ∑ x, ∑ y, (if x < y then j x * j y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm]
  calc (∑ x, j x) ^ 2 = ∑ x, ∑ y, j x * j y := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ x, ∑ y, ((if x < y then j x * j y else 0)
      + (if y < x then j x * j y else 0) + (if x = y then j x ^ 2 else 0)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h1 x y
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, if_true]
      rw [h2]; ring
end Formalism.HermitianLatticeCounting.P
