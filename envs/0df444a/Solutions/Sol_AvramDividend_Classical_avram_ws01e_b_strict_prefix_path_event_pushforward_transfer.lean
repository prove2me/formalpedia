-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_prefix_path_event_pushforward_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:11:37.630999+00:00
-- url     : https://prove2.me/submissions/cad03cd5-7bde-4620-a1da-2b57d12edef0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (a : ℝ)
    (F : Ω → (Fin n → ℝ)) (hF : Measurable F)
    (w : (Fin n → ℝ) → ℕ → ℝ)
    (hw : ∀ j : ℕ, Measurable (fun v : Fin n → ℝ => w v j))
    (Z : ℕ → Ω → ℝ)
    (hprefix : ∀ (ω : Ω) (k : ℕ), k ≤ n →
      Finset.sum (Finset.range k) (w (F ω)) =
        Z k ω - Z 0 ω)
    (hLaw :
      (Measure.map F ν)
        {v : Fin n → ℝ | ∃ k : Fin n.succ,
          Finset.sum (Finset.range n) (w v) -
            Finset.sum (Finset.range k.val) (w v) < a} =
      (Measure.map F ν)
        {v : Fin n → ℝ | ∃ k : Fin n.succ,
          Finset.sum (Finset.range k.val) (w v) < a}) :
    ν {ω : Ω | ∃ k : Fin n.succ, Z n ω - Z k.val ω < a} =
    ν {ω : Ω | ∃ k : Fin n.succ, Z k.val ω - Z 0 ω < a} := by
  let pref : (Fin n → ℝ) → ℕ → ℝ :=
    fun v k => Finset.sum (Finset.range k) (w v)
  let L : Set (Fin n → ℝ) :=
    {v | ∃ k : Fin n.succ, pref v n - pref v k.val < a}
  let R : Set (Fin n → ℝ) :=
    {v | ∃ k : Fin n.succ, pref v k.val < a}
  have hpref (k : ℕ) : Measurable (fun v : Fin n → ℝ => pref v k) :=
    Finset.measurable_sum _ (fun j _ => hw j)
  have hL : MeasurableSet L := by
    have hu : MeasurableSet (⋃ k : Fin n.succ,
        {v : Fin n → ℝ | pref v n - pref v k.val < a}) :=
      MeasurableSet.iUnion (fun k =>
        measurableSet_lt ((hpref n).sub (hpref k.val)) measurable_const)
    simpa only [L, Set.setOf_exists] using hu
  have hR : MeasurableSet R := by
    have hu : MeasurableSet (⋃ k : Fin n.succ,
        {v : Fin n → ℝ | pref v k.val < a}) :=
      MeasurableSet.iUnion (fun k =>
        measurableSet_lt (hpref k.val) measurable_const)
    simpa only [R, Set.setOf_exists] using hu
  have hprefix' (ω : Ω) (k : ℕ) (hk : k ≤ n) :
      pref (F ω) k = Z k ω - Z 0 ω :=
    hprefix ω k hk
  have hEL (ω : Ω) : (∃ k : Fin n.succ,
      Z n ω - Z k.val ω < a) ↔ F ω ∈ L := by
    change (∃ k : Fin n.succ, Z n ω - Z k.val ω < a) ↔
      (∃ k : Fin n.succ, pref (F ω) n - pref (F ω) k.val < a)
    apply exists_congr
    intro k
    rw [hprefix' ω n le_rfl,
      hprefix' ω k.val (Nat.le_of_lt_succ k.isLt)]
    constructor <;> intro h <;> linarith
  have hER (ω : Ω) : (∃ k : Fin n.succ,
      Z k.val ω - Z 0 ω < a) ↔ F ω ∈ R := by
    change (∃ k : Fin n.succ, Z k.val ω - Z 0 ω < a) ↔
      (∃ k : Fin n.succ, pref (F ω) k.val < a)
    apply exists_congr
    intro k
    rw [hprefix' ω k.val (Nat.le_of_lt_succ k.isLt)]
  calc
    ν {ω : Ω | ∃ k : Fin n.succ, Z n ω - Z k.val ω < a} =
      (Measure.map F ν) L := by
        rw [Measure.map_apply hF hL]
        congr 1; ext ω; exact hEL ω
    _ = (Measure.map F ν) R := hLaw
    _ = ν {ω : Ω | ∃ k : Fin n.succ,
          Z k.val ω - Z 0 ω < a} := by
        rw [Measure.map_apply hF hR]
        congr 1; ext ω; exact (hER ω).symm
