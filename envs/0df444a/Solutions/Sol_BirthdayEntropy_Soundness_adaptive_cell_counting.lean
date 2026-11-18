-- Prove2me | solution 1 for BirthdayEntropy.Soundness.adaptive_cell_counting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:40:09.647855+00:00
-- url     : https://prove2.me/submissions/e6d3f0b8-33b1-4b65-819d-12f45b0362bb

import Theorems.Thm_BirthdayEntropy_Soundness_entropy_cell_counting
import Theorems.Thm_OAI_ThorpCompatibility_Law_gibbs_le
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

private lemma uniform_entropy {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty) :
    (uniformOn Ω hΩ).entropy = Real.log (Ω.card : ℝ) := by
  rw [Law.entropy, uniform_mean]
  have heq : ∑ a ∈ Ω, Real.log ((uniformOn Ω hΩ).mass a) =
      (Ω.card : ℝ) * Real.log (1 / (Ω.card : ℝ)) := by
    calc
      _ = ∑ a ∈ Ω, Real.log (1 / (Ω.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [uniform_mass, if_pos ha]
      _ = _ := by simp
  rw [heq]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hΩ.card_pos.ne')]
  simp

private lemma entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] (Q : Law α) :
    Q.entropy ≤ Real.log (Fintype.card α : ℝ) := by
  have h := Q.gibbs_le (fun _ => 1) (by intro; norm_num) (by simp; positivity) (by simp)
  simpa [Law.mean, Law.entropy] using h

private lemma uniform_mean_mul {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (c : ℝ) (f : α → ℝ) : (uniformOn Ω hΩ).mean (fun a => c * f a) =
      c * (uniformOn Ω hΩ).mean f := by
  rw [uniform_mean, uniform_mean, ← Finset.mul_sum, mul_div_assoc]

theorem solution {V τ : Type*} [Fintype V] [Fintype τ]
    (r : ℕ) (Ω : Finset ((Fin r → V) × (Fin r → V))) (hΩ : Ω.Nonempty)
    (F : ((Fin r → V) × (Fin r → V)) → τ) (R : τ → ℝ)
    (hR : ∀ f, 0 ≤ R f) (a b h κ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h) (hκ : 0 ≤ κ)
    (hcell : ∀ f, ((cell Ω F f).card : ℝ) ≤
      (Fintype.card V : ℝ)^(2*r) * Real.exp (-a * R f)) :
    let Q := uniformOn Ω hΩ
    let E := Q.mean (fun X => R (F X))
    let p := (Ω.card : ℝ) / (Fintype.card V : ℝ)^(2*r)
    (Q.map F).entropy ≤ κ * mutualInfo Q Prod.fst Prod.snd + b * E + h →
      (a-b) * E - h ≤ (1+κ) * Real.log (1/p) ∧
      ∀ R₀ : ℝ, b ≤ a →
        (∀ f, (cell Ω F f).Nonempty → R₀ ≤ R f) →
        (a-b) * R₀ - h ≤ (a-b) * E - h := by
  classical
  dsimp only
  let Q := uniformOn Ω hΩ
  let E := Q.mean (fun X => R (F X))
  let M : ℝ := (Fintype.card V : ℝ)^(2*r)
  letI : Nonempty (Fin r → V) := ⟨hΩ.choose.1⟩
  have hM : 0 < M := by
    have hc : 0 < Fintype.card ((Fin r → V) × (Fin r → V)) := Fintype.card_pos
    have heq : (Fintype.card ((Fin r → V) × (Fin r → V)) : ℝ) = M := by
      simp [M, Fintype.card_prod, Fintype.card_fun, pow_mul, pow_two]
      ring
    rw [← heq]
    exact_mod_cast hc
  have hΩpos : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hMI : mutualInfo Q Prod.fst Prod.snd ≤ Real.log (M / Ω.card) := by
    have hL := entropy_le_log_card (Q.map Prod.fst)
    have hR := entropy_le_log_card (Q.map Prod.snd)
    have hmap : Q.map (fun a => (a.1, a.2)) = Q := by
      apply Law.ext
      intro a
      simp [Law.map]
    unfold mutualInfo
    rw [hmap, show Q.entropy = Real.log (Ω.card : ℝ) from uniform_entropy Ω hΩ]
    rw [Real.log_div hM.ne' hΩpos.ne']
    have heq : Real.log M = 2 * Real.log (Fintype.card (Fin r → V) : ℝ) := by
      simp [M, Fintype.card_fun, Nat.cast_pow, Real.log_pow]
      ring
    linarith
  have hc := (entropy_cell_counting Ω hΩ F (fun f => M * Real.exp (-a * R f))
      (fun f _ => hcell f)).2 M (fun f => a * R f) (by intro f hf; simp only [neg_mul]; exact le_rfl)
  have hmean : (uniformOn Ω hΩ).mean (fun x => a * R (F x)) = a * E := by
    exact uniform_mean_mul Ω hΩ a _
  rw [hmean] at hc
  intro hent
  have hlog : Real.log (1 / ((Ω.card : ℝ) / M)) = Real.log (M / Ω.card) := by
    congr 1
    field_simp
  rw [hlog]
  refine ⟨?_, ?_⟩
  · have hκMI := mul_le_mul_of_nonneg_left hMI hκ
    change (Q.map F).entropy ≤ κ * mutualInfo Q Prod.fst Prod.snd + b * E + h at hent
    change a * E - (Q.map F).entropy ≤ Real.log (M / Ω.card) at hc
    linarith
  · intro R₀ hba hfloor
    have he : R₀ ≤ E := by
      have he := uniform_mean_le Ω hΩ (fun _ => R₀) (fun X => R (F X))
        (fun X hX => hfloor _ (cell_nonempty Ω F hX))
      rw [uniform_mean_const] at he
      exact he
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hba)) h
