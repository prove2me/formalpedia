-- Prove2me | solution 1 for Formalism.QuantumDeterminants.holomorphicFormalDegree_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:37.905095+00:00
-- url     : https://prove2.me/submissions/315901c9-3524-4044-88ed-83e515d99989

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.REAL
noncomputable section
namespace Formalism.QuantumDeterminants
private theorem fdegDen_ne_zero (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a _
  rw [Finset.prod_ne_zero_iff]
  intro b hb
  have hab : a < b := by simpa using hb
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith
private theorem prod_pairs_succ {n : ℕ} (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∏ x : Fin (n + 1), ∏ y ∈ univ.filter (fun y : Fin (n + 1) => x < y), f x y) =
      (∏ j : Fin n, f 0 j.succ) *
        ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), f i.succ j.succ := by
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]
end Formalism.QuantumDeterminants
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : HolFdeg := by
  intro n a b hn
  unfold fdegHC
  rw [prod_pairs_succ, prod_pairs_succ]
  have hpair : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
      |lamHol n a b i.succ - lamHol n a b j.succ| =
      ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
        (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := by simpa using hj
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    simp only [lamHol, Fin.succ_ne_zero, if_false, Fin.val_succ]
    push_cast
    rw [abs_of_nonneg (by linarith)]
    ring
  have hP : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
      (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) ≠ 0 := by
    have e : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
        (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) =
        ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) :=
      Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
        simp only [Fin.val_succ]; push_cast; ring
    rw [e]; exact fdegDen_ne_zero n
  rw [hpair, mul_div_mul_right _ _ hP]
  have hB : ∏ j : Fin n, (((j.succ : ℕ) : ℝ) - (((0 : Fin (n + 1)) : ℕ) : ℝ)) = (n.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => (j : ℝ) + 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Fin.val_succ]
  have hA : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| =
      ∏ j ∈ Icc 1 n, (b - a - (j : ℝ)) := by
    have e1 : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| =
        ∏ j ∈ range n, (b - a - n + (j : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => b - a - n + (j : ℝ))]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [lamHol, Fin.succ_ne_zero, if_false, if_true, Fin.val_succ]
      push_cast
      rw [abs_of_nonneg (by have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)]
      ring
    have eI : Icc 1 n = Ico 1 (n + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, ← Finset.prod_range_reflect, eI, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    have e : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; push_cast; ring
  rw [hA, hB]
end Formalism.QuantumDeterminants
