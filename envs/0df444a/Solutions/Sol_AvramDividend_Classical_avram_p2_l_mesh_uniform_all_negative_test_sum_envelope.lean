-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_test_sum_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:33:39.826533+00:00
-- url     : https://prove2.me/submissions/12340ffc-8afa-4035-9a0b-2bfe87e2be6d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_mark_count_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- One grid threshold bounds *every* bounded negative-supported test sum,
even when tests are discontinuous and the marked set has boundary atoms. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = 0) →
        ∀ M : ℝ, 0 ≤ M → (∀ z : ℝ, |f z| ≤ M) →
        |∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))| ≤
          (S.card : ℝ) * M := by
  classical
  have hfinite
      (s : Finset ℕ) (v : ℕ → ℝ) (M : ℝ)
      (hv : ∀ a, |v a| ≤ M) :
      |∑ a ∈ s, v a| ≤
        ((s.filter (fun a => v a ≠ 0)).card : ℝ) * M := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      by_cases hzero : v a = 0
      · simpa [Finset.sum_insert ha, Finset.filter_insert,
          hzero, ha] using ih
      · have hcount :
            ((insert a s).filter (fun x => v x ≠ 0)).card =
              (s.filter (fun x => v x ≠ 0)).card + 1 := by
          simp [Finset.filter_insert, ha, hzero]
        calc
          |∑ x ∈ insert a s, v x| = |v a + ∑ x ∈ s, v x| := by
            rw [Finset.sum_insert ha]
          _ ≤ |v a| + |∑ x ∈ s, v x| := abs_add_le _ _
          _ ≤ M + ((s.filter (fun x => v x ≠ 0)).card : ℝ) * M :=
            add_le_add (hv a) ih
          _ = (((insert a s).filter (fun x => v x ≠ 0)).card : ℝ) * M := by
            rw [hcount]
            push_cast
            ring
  obtain ⟨S, hS, hcount⟩ :=
    avram_p2_l_mesh_uniform_all_negative_mark_count_envelope
      Y T hT ρ hρ hL hR
  refine ⟨S, hS, ?_⟩
  filter_upwards [hcount] with n hn
  intro f hfzero M hM hfM
  let B : Set ℝ := {z | f z ≠ 0}
  have hBsep : B ⊆ Iic (-ρ) := by
    intro z hz
    change z ≤ -ρ
    apply le_of_not_gt
    intro hgt
    exact hz (hfzero z hgt)
  have hcard := hn B hBsep
  let v : ℕ → ℝ := fun i =>
    f (Y (((i + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))) -
      Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
  have hv : ∀ i, |v i| ≤ M := fun _ => hfM _
  have hn : ((Finset.range (n + 1)).filter
      (fun i => v i ≠ 0)).card ≤ S.card := by
    simpa only [v, B, Set.mem_setOf_eq] using hcard
  have hc :
      (((Finset.range (n + 1)).filter (fun i => v i ≠ 0)).card : ℝ) ≤
      (S.card : ℝ) := by
    exact_mod_cast hn
  have hmul :
      (((Finset.range (n + 1)).filter (fun i => v i ≠ 0)).card : ℝ) * M ≤
        (S.card : ℝ) * M := mul_le_mul_of_nonneg_right hc hM
  have hfinitebound :
      |∑ i ∈ Finset.range (n + 1), v i| ≤
        (((Finset.range (n + 1)).filter (fun i => v i ≠ 0)).card : ℝ) * M :=
    hfinite (Finset.range (n + 1)) v M hv
  have hs := hfinitebound.trans hmul
  simpa only [v, B, Set.mem_setOf_eq] using hs
