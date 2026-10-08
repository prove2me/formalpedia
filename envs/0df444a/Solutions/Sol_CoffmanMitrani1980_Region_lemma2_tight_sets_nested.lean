-- Prove2me | solution 1 for CoffmanMitrani1980.Region.lemma2_tight_sets_nested
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:32:17.721816+00:00
-- url     : https://prove2.me/submissions/081adcc4-4f81-4d33-84f2-17e6ff10cb00

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

set_option autoImplicit false

open Finset

lemma cm8903_key (x x1 x2 r r1 r2 : ℝ) (hx : 0 ≤ x) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hr : 0 ≤ r) (hr1 : 0 < r1) (hr2 : 0 < r2) (h : r + r1 + r2 < 1) :
    (x + x1) / (1 - (r + r1)) + (x + x2) / (1 - (r + r2)) <
      (x + x1 + x2) / (1 - (r + r1 + r2)) + x / (1 - r) := by
  have hD : 0 < 1 - r := by linarith
  have hD1 : 0 < 1 - (r + r1) := by linarith
  have hD2 : 0 < 1 - (r + r2) := by linarith
  have hD12 : 0 < 1 - (r + r1 + r2) := by linarith
  have e1 : (x + x1 + x2) / (1 - (r + r1 + r2)) - (x + x1) / (1 - (r + r1)) =
      x2 / (1 - (r + r1 + r2)) + (x + x1) * r2 / ((1 - (r + r1)) * (1 - (r + r1 + r2))) := by
    field_simp
    ring
  have e2 : (x + x2) / (1 - (r + r2)) - x / (1 - r) =
      x2 / (1 - (r + r2)) + x * r2 / ((1 - r) * (1 - (r + r2))) := by
    field_simp
    ring
  have i1 : x2 / (1 - (r + r2)) < x2 / (1 - (r + r1 + r2)) :=
    div_lt_div_of_pos_left hx2 hD12 (by linarith)
  have i2 : x * r2 / ((1 - r) * (1 - (r + r2))) ≤
      (x + x1) * r2 / ((1 - (r + r1)) * (1 - (r + r1 + r2))) := by
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hr2.le)
      (by positivity)
    exact mul_le_mul (by linarith) (by linarith) hD12.le hD.le
  linarith

open CoffmanMitrani1980.Region in
theorem solution {M : ℕ} (p : Params M) (W : Fin M → ℝ) (hW : W ∈ p.Hss)
    (g₁ g₂ : Finset (Fin M)) (hg₁ : g₁.Nonempty) (hg₂ : g₂.Nonempty)
    (ht₁ : ∑ i ∈ g₁, p.rho i * W i = p.f g₁) (ht₂ : ∑ i ∈ g₂, p.rho i * W i = p.f g₂) :
    g₁ ⊆ g₂ ∨ g₂ ⊆ g₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n21⟩ := hcon
  have hrho : ∀ i, 0 < p.rho i := fun i => div_pos (p.lam_pos i) (p.mu_pos i)
  have ha : ∀ i, 0 < p.a i := fun i => div_pos (hrho i) (p.mu_pos i)
  have hne1 : (g₁ \ g₂).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n12
  have hne2 : (g₂ \ g₁).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n21
  -- decomposition of sums
  have dec1 : ∀ c : Fin M → ℝ, ∑ i ∈ g₁, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i :=
    fun c => (Finset.sum_inter_add_sum_sdiff g₁ g₂ c).symm
  have dec2 : ∀ c : Fin M → ℝ, ∑ i ∈ g₂, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c; rw [Finset.inter_comm]; exact (Finset.sum_inter_add_sum_sdiff g₂ g₁ c).symm
  have decU : ∀ c : Fin M → ℝ, ∑ i ∈ g₁ ∪ g₂, c i =
      ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c
    have := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := c)
    rw [dec1 c, dec2 c] at this
    linarith
  have hRlt : ∑ i ∈ g₁ ∪ g₂, p.rho i < 1 := by
    have h1 : ∑ i ∈ g₁ ∪ g₂, p.rho i ≤ ∑ i, p.rho i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (hrho i).le)
    have h2 : ∑ i, p.rho i < 1 := p.load_lt_one
    linarith
  -- f(∪) ≤ S(∪)
  have hU : p.f (g₁ ∪ g₂) ≤ ∑ i ∈ g₁ ∪ g₂, p.rho i * W i := by
    by_cases hu : g₁ ∪ g₂ = univ
    · rw [hu, hW.1]
      apply le_of_eq
      unfold Params.f Params.V
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      unfold Params.a Params.rho
      have := p.mu_pos i
      field_simp
    · exact hW.2 _ (hg₁.mono Finset.subset_union_left) hu
  have hI : p.f (g₁ ∩ g₂) ≤ ∑ i ∈ g₁ ∩ g₂, p.rho i * W i := by
    rcases (g₁ ∩ g₂).eq_empty_or_nonempty with he | hne
    · rw [he]; simp [Params.f]
    · have hnu : g₁ ∩ g₂ ≠ univ := by
        intro hu
        apply n12
        intro x _
        have : x ∈ g₁ ∩ g₂ := hu ▸ Finset.mem_univ x
        exact (Finset.mem_inter.1 this).2
      exact hW.2 _ hne hnu
  have key := cm8903_key (∑ i ∈ g₁ ∩ g₂, p.a i) (∑ i ∈ g₁ \ g₂, p.a i) (∑ i ∈ g₂ \ g₁, p.a i)
    (∑ i ∈ g₁ ∩ g₂, p.rho i) (∑ i ∈ g₁ \ g₂, p.rho i) (∑ i ∈ g₂ \ g₁, p.rho i)
    (Finset.sum_nonneg fun i _ => (ha i).le) (Finset.sum_pos (fun i _ => ha i) hne1)
    (Finset.sum_pos (fun i _ => ha i) hne2) (Finset.sum_nonneg fun i _ => (hrho i).le)
    (Finset.sum_pos (fun i _ => hrho i) hne1) (Finset.sum_pos (fun i _ => hrho i) hne2)
    (by rw [← decU]; exact hRlt)
  have hf1 : p.f g₁ = (∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₁ \ g₂, p.a i) /
      (1 - (∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₁ \ g₂, p.rho i)) := by
    unfold Params.f; rw [dec1, dec1 p.rho]
  have hf2 : p.f g₂ = (∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₂ \ g₁, p.a i) /
      (1 - (∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₂ \ g₁, p.rho i)) := by
    unfold Params.f; rw [dec2, dec2 p.rho]
  have hfU : p.f (g₁ ∪ g₂) = (∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₁ \ g₂, p.a i
      + ∑ i ∈ g₂ \ g₁, p.a i) / (1 - (∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₁ \ g₂, p.rho i
      + ∑ i ∈ g₂ \ g₁, p.rho i)) := by
    unfold Params.f; rw [decU, decU p.rho]
  have hfI : p.f (g₁ ∩ g₂) = (∑ i ∈ g₁ ∩ g₂, p.a i) / (1 - ∑ i ∈ g₁ ∩ g₂, p.rho i) := rfl
  have hS := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := fun i => p.rho i * W i)
  rw [← hf1, ← hf2, ← hfU, ← hfI] at key
  linarith
