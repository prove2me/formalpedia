-- Prove2me | solution 1 for BirthdayEntropy.Soundness.entropy_cell_counting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:37:48.433841+00:00
-- url     : https://prove2.me/submissions/32722c86-6f9b-4005-b50b-9d01d537078b

import Definitions.Def_BirthdayEntropy_Soundness_Counting
noncomputable section
open scoped Classical
open Finset OAI.ThorpCompatibility BirthdayEntropy.Soundness

private lemma mean_map {α τ : Type*} [Fintype α] [Fintype τ]
    (Q : Law α) (F : α → τ) (g : τ → ℝ) :
    (Q.map F).mean g = Q.mean (fun a => g (F a)) := by
  classical
  unfold Law.mean Law.map
  simp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext a
  simp

private lemma uniform_mass {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (a : α) : (uniformOn Ω hΩ).mass a = if a ∈ Ω then 1 / (Ω.card : ℝ) else 0 := by
  classical
  unfold uniformOn Law.map Law.uniform
  simp only
  change (∑ x : Ω, if x.val = a then 1 / (Fintype.card Ω : ℝ) else 0) = _
  rw [Finset.sum_coe_sort Ω (fun x : α => if x = a then 1 / (Fintype.card Ω : ℝ) else 0)]
  simp

private lemma uniform_mean {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (g : α → ℝ) : (uniformOn Ω hΩ).mean g = (∑ a ∈ Ω, g a) / Ω.card := by
  classical
  unfold Law.mean
  simp_rw [uniform_mass, ite_mul, zero_mul]
  simp [Finset.sum_filter, Finset.sum_mul, div_eq_mul_inv, mul_comm]

private lemma uniform_map_mass {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) (f : τ) :
    ((uniformOn Ω hΩ).map F).mass f = ((cell Ω F f).card : ℝ) / Ω.card := by
  classical
  unfold Law.map
  simp only
  simp_rw [uniform_mass]
  have hf : Finset.univ.filter (fun x => F x = f) ∩ Ω = cell Ω F f := by
    ext a
    simp [cell, and_comm]
  simp [Finset.sum_ite, hf, div_eq_mul_inv]

private lemma uniform_mean_le {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (f g : α → ℝ) (h : ∀ a ∈ Ω, f a ≤ g a) :
    (uniformOn Ω hΩ).mean f ≤ (uniformOn Ω hΩ).mean g := by
  rw [uniform_mean, uniform_mean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (by positivity)

private lemma uniform_mean_const {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (c : ℝ) : (uniformOn Ω hΩ).mean (fun _ => c) = c := by
  rw [uniform_mean]
  simp [hΩ.card_pos.ne', mul_div_cancel_left₀]

private lemma uniform_mean_sub {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (f g : α → ℝ) : (uniformOn Ω hΩ).mean (fun a => f a - g a) =
      (uniformOn Ω hΩ).mean f - (uniformOn Ω hΩ).mean g := by
  simp [uniform_mean, Finset.sum_sub_distrib, sub_div]

private lemma cell_nonempty {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (F : α → τ) {a : α} (ha : a ∈ Ω) : (cell Ω F (F a)).Nonempty := by
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩

private lemma entropy_identity {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) :
    ((uniformOn Ω hΩ).map F).entropy = Real.log (Ω.card : ℝ) -
      (uniformOn Ω hΩ).mean (fun a => Real.log ((cell Ω F (F a)).card : ℝ)) := by
  rw [Law.entropy, mean_map]
  have heq : (uniformOn Ω hΩ).mean (fun a => Real.log (((uniformOn Ω hΩ).map F).mass (F a))) =
      (uniformOn Ω hΩ).mean (fun a => Real.log ((cell Ω F (F a)).card : ℝ) - Real.log (Ω.card : ℝ)) := by
    rw [uniform_mean, uniform_mean]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [uniform_map_mass, Real.log_div]
    · exact_mod_cast (cell_nonempty Ω F ha).card_pos.ne'
    · exact_mod_cast hΩ.card_pos.ne'
  rw [heq, uniform_mean_sub, uniform_mean_const]
  ring

theorem solution {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) (Mcell : τ → ℝ)
    (hcell : ∀ f, (cell Ω F f).Nonempty → ((cell Ω F f).card : ℝ) ≤ Mcell f) :
    let Q := uniformOn Ω hΩ
    Real.log (Ω.card : ℝ) ≤ (Q.map F).entropy + Q.mean (fun a => Real.log (Mcell (F a))) ∧
    ∀ (M : ℝ) (s : τ → ℝ),
      (∀ f, (cell Ω F f).Nonempty → Mcell f ≤ M * Real.exp (-s f)) →
      Q.mean (fun a => s (F a)) - (Q.map F).entropy ≤ Real.log (M / Ω.card) := by
  classical
  dsimp only
  have hpos : ∀ a ∈ Ω, 0 < ((cell Ω F (F a)).card : ℝ) := by
    intro a ha
    exact_mod_cast (cell_nonempty Ω F ha).card_pos
  have hMpos : ∀ a ∈ Ω, 0 < Mcell (F a) := by
    intro a ha
    exact lt_of_lt_of_le (hpos a ha) (hcell _ (cell_nonempty Ω F ha))
  have hfirst : Real.log (Ω.card : ℝ) ≤ ((uniformOn Ω hΩ).map F).entropy +
      (uniformOn Ω hΩ).mean (fun a => Real.log (Mcell (F a))) := by
    rw [entropy_identity]
    have := uniform_mean_le Ω hΩ _ _ (fun a ha =>
      Real.log_le_log (hpos a ha) (hcell _ (cell_nonempty Ω F ha)))
    linarith
  refine ⟨hfirst, ?_⟩
  intro M s hbound
  have hMp : 0 < M := by
    obtain ⟨a, ha⟩ := hΩ
    have := lt_of_lt_of_le (hMpos a ha) (hbound _ (cell_nonempty Ω F ha))
    exact pos_of_mul_pos_left this (Real.exp_pos _).le
  have hlog : ∀ a ∈ Ω, Real.log (Mcell (F a)) ≤ Real.log M - s (F a) := by
    intro a ha
    calc
      Real.log (Mcell (F a)) ≤ Real.log (M * Real.exp (-s (F a))) :=
        Real.log_le_log (hMpos a ha) (hbound _ (cell_nonempty Ω F ha))
      _ = Real.log M - s (F a) := by rw [Real.log_mul hMp.ne' (Real.exp_ne_zero _), Real.log_exp]; ring
  have hmean := uniform_mean_le Ω hΩ _ _ hlog
  rw [uniform_mean_sub, uniform_mean_const] at hmean
  rw [Real.log_div hMp.ne' (by exact_mod_cast hΩ.card_pos.ne')]
  linarith
