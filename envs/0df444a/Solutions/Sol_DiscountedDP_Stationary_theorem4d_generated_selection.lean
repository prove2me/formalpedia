-- Prove2me | solution 1 for DiscountedDP.Stationary.theorem4d_generated_selection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:02:50.193345+00:00
-- url     : https://prove2.me/submissions/e4ae1df4-0905-4112-b5d6-a9bbac4d403d

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators



namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

lemma t4_T_measurable (P : Problem S A) (f : {g : S → A // Measurable g})
    (u : S → ℝ) (hu : IsBM u) : Measurable (T P f u) := by
  haveI := P.q_markov
  have hm : Measurable (fun s : S => (s, f.1 s)) := measurable_id.prodMk f.2
  let κ := P.q.comap (fun s : S => (s, f.1 s)) hm
  have h : StronglyMeasurable (fun s => ∫ s', P.r (s, f.1 s, s') + P.β * u s' ∂κ s) := by
    apply StronglyMeasurable.integral_kernel_prod_right
      (f := fun s s' => P.r (s, f.1 s, s') + P.β * u s')
    apply Measurable.stronglyMeasurable
    apply Measurable.add
    · exact P.r_measurable.comp (measurable_fst.prodMk ((f.2.comp measurable_fst).prodMk measurable_snd))
    · exact (hu.1.comp measurable_snd).const_mul _
  exact h.measurable

lemma t4_T_bound (P : Problem S A) (f : {g : S → A // Measurable g})
    (u : S → ℝ) (Cr Cu : ℝ) (hr : ∀ x, |P.r x| ≤ Cr) (hu : ∀ s, |u s| ≤ Cu) (s : S) :
    |T P f u s| ≤ Cr + P.β * Cu := by
  haveI := P.q_markov
  have := norm_integral_le_of_norm_le_const (μ := P.q (s, f.1 s))
    (f := fun s' => P.r (s, f.1 s, s') + P.β * u s') (C := Cr + P.β * Cu)
    (Filter.Eventually.of_forall (fun s' => by
      simp only [Real.norm_eq_abs]
      calc |P.r (s, f.1 s, s') + P.β * u s'| ≤ |P.r (s, f.1 s, s')| + |P.β * u s'| := abs_add_le _ _
        _ ≤ Cr + P.β * Cu := by
          rw [abs_mul, abs_of_nonneg P.β_nonneg]
          exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (hu s') P.β_nonneg)))
  simpa [T] using this

theorem theorem4d_core
    (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ)
    (hu : IsBM u) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
      ∀ s, U P π u s - ε ≤ T P f u s := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hbdd : ∀ s, BddAbove (Set.range fun n => T P (π n) u s) := by
    intro s
    refine ⟨Cr + P.β * Cu, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (le_abs_self _).trans (t4_T_bound P (π n) u Cr Cu hr hCu s)
  have hex : ∀ s, ∃ n, U P π u s - ε < T P (π n) u s := by
    intro s
    exact exists_lt_of_lt_ciSup (by unfold U; linarith : U P π u s - ε < ⨆ n, T P (π n) u s)
  have hUm : Measurable (U P π u) := by
    unfold U
    exact Measurable.iSup (fun n => t4_T_measurable P (π n) u hu)
  have hset : ∀ n, MeasurableSet {s | U P π u s - ε < T P (π n) u s} := fun n =>
    measurableSet_lt (hUm.sub_const ε) (t4_T_measurable P (π n) u hu)
  classical
  let N : S → ℕ := fun s => Nat.find (hex s)
  have hN : Measurable N := measurable_find (p := fun s n => U P π u s - ε < T P (π n) u s) hex hset
  have hfm : Measurable (fun s => (π (N s)).1 s) :=
    Measurable.find (f := fun n s => (π n).1 s) (p := fun n s => U P π u s - ε < T P (π n) u s)
      (fun n => (π n).2) hset hex
  refine ⟨⟨fun s => (π (N s)).1 s, hfm⟩, ⟨fun n => N ⁻¹' {n}, fun n => hN (measurableSet_singleton n), ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr (fun s hi hj => hij (by simp at hi hj; omega))
  · ext s; simp
  · intro n s hs
    simp at hs
    simp [hs]
  · intro s
    exact (Nat.find_spec (hex s)).le

end DiscountedDP.Stationary

open DiscountedDP.Stationary


theorem solution
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ)
    (hu : IsBM u) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
      ∀ s, U P π u s - ε ≤ T P f u s := by
  exact theorem4d_core P π u hu ε hε
