-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.weighted_off_diagonal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:32.643922+00:00
-- url     : https://prove2.me/submissions/c157a1ee-0357-420b-b745-798014295dc6

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_WeightedOffDiagonalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Formalism.NuclearRankWeightBounds.D
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.WeightedOff := by
  intro N s ep h Y hY hz hh
  classical
  obtain ⟨T, hT⟩ : ∃ T : Fin N → Fin N → ℝ,
      T = fun a b => ∑ i ∈ Ico 1 N, if a.val < i ∧ i ≤ b.val then s i else 0 := ⟨_, rfl⟩
  have hsym : ∀ a b, ‖Y b a‖ = ‖Y a b‖ := by
    intro a b
    rw [← hY.apply b a, norm_star]
  have hTlt : ∀ a b : Fin N, a < b → T a b = ∑ i ∈ Ico (a.val + 1) (b.val + 1), s i := by
    intro a b hab
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    rw [hT]
    simp only
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hTgt : ∀ a b : Fin N, a < b → T b a = 0 := by
    intro a b hab
    have hab' : a.val < b.val := hab
    rw [hT]
    simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    omega
  have hpt : ∀ a b, h * ‖Y a b‖ ^ 2 ≤ ‖Y a b‖ ^ 2 * T a b + ‖Y b a‖ ^ 2 * T b a := by
    intro a b
    by_cases he : ep a = ep b
    · simp [hz a b he, hz b a he.symm]
    rw [hsym a b]
    rcases lt_trichotomy a b with hab | hab | hab
    · have h3 := hh b a hab (fun e => he e.symm)
      rw [hTgt a b hab, mul_zero, add_zero, mul_comm, hTlt a b hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    · exact absurd (congrArg ep hab) he
    · have h3 := hh a b hab he
      rw [hTgt b a hab, mul_zero, zero_add, mul_comm, hTlt b a hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hi : ∀ i : ℕ, (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
      ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, if a.val < i ∧ i ≤ b.val then ‖Y a b‖ ^ 2 else 0 := by
    intro i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    by_cases ha : a.val < i <;> simp [ha]
  have hrhs : (∑ i ∈ Ico 1 N, s i *
      ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b := by
    simp_rw [hi, hT, Finset.mul_sum]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hhs : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)
  have hswap : (∑ a, ∑ b, ‖Y b a‖ ^ 2 * T b a) = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b :=
    Finset.sum_comm
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => hpt a b))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  rw [hrhs, hhs]
  linarith
end Formalism.NuclearRankWeightBounds.P
