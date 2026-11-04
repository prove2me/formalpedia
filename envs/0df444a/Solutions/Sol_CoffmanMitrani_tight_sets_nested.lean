-- Prove2me | solution 1 for CoffmanMitrani.tight_sets_nested
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T04:04:27.86514+00:00
-- url     : https://prove2.me/submissions/a8acacbb-788f-49c8-927f-b58f28d5ee2c

import Mathlib
import Definitions.Def_CoffmanMitrani_Hss

set_option autoImplicit false

open Finset

theorem cm_5a81ea39_key (x x1 x2 r r1 r2 : ℝ) (hx : 0 ≤ x) (hx1 : 0 < x1) (hx2 : 0 < x2)
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

theorem cm_5a81ea39_aux {ι : Type} [Fintype ι] [DecidableEq ι] (a r W : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hrho : ∀ i, 0 < r i) (hlt : ∑ i, r i < 1)
    (hcons : ∑ i, r i * W i = (∑ i, a i) / (1 - ∑ i, r i))
    (hineq : ∀ g : Finset ι, g.Nonempty → g ≠ Finset.univ →
      (∑ i ∈ g, a i) / (1 - ∑ i ∈ g, r i) ≤ ∑ i ∈ g, r i * W i)
    (g₁ g₂ : Finset ι) (hg₁ : g₁.Nonempty)
    (ht₁ : ∑ i ∈ g₁, r i * W i = (∑ i ∈ g₁, a i) / (1 - ∑ i ∈ g₁, r i))
    (ht₂ : ∑ i ∈ g₂, r i * W i = (∑ i ∈ g₂, a i) / (1 - ∑ i ∈ g₂, r i)) :
    g₁ ⊆ g₂ ∨ g₂ ⊆ g₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n21⟩ := hcon
  have hne1 : (g₁ \ g₂).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n12
  have hne2 : (g₂ \ g₁).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n21
  have dec1 : ∀ c : ι → ℝ, ∑ i ∈ g₁, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i :=
    fun c => (Finset.sum_inter_add_sum_sdiff g₁ g₂ c).symm
  have dec2 : ∀ c : ι → ℝ, ∑ i ∈ g₂, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c; rw [Finset.inter_comm]; exact (Finset.sum_inter_add_sum_sdiff g₂ g₁ c).symm
  have decU : ∀ c : ι → ℝ, ∑ i ∈ g₁ ∪ g₂, c i =
      ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c
    have := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := c)
    rw [dec1 c, dec2 c] at this
    linarith
  have hRlt : ∑ i ∈ g₁ ∪ g₂, r i < 1 := by
    have h1 : ∑ i ∈ g₁ ∪ g₂, r i ≤ ∑ i, r i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (hrho i).le)
    linarith
  have hU : (∑ i ∈ g₁ ∪ g₂, a i) / (1 - ∑ i ∈ g₁ ∪ g₂, r i) ≤
      ∑ i ∈ g₁ ∪ g₂, r i * W i := by
    by_cases hu : g₁ ∪ g₂ = Finset.univ
    · rw [hu, hcons]
    · exact hineq _ (hg₁.mono Finset.subset_union_left) hu
  have hI : (∑ i ∈ g₁ ∩ g₂, a i) / (1 - ∑ i ∈ g₁ ∩ g₂, r i) ≤
      ∑ i ∈ g₁ ∩ g₂, r i * W i := by
    rcases (g₁ ∩ g₂).eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · have hnu : g₁ ∩ g₂ ≠ Finset.univ := by
        intro hu
        apply n12
        intro x _
        have : x ∈ g₁ ∩ g₂ := hu ▸ Finset.mem_univ x
        exact (Finset.mem_inter.1 this).2
      exact hineq _ hne hnu
  have key := cm_5a81ea39_key (∑ i ∈ g₁ ∩ g₂, a i) (∑ i ∈ g₁ \ g₂, a i) (∑ i ∈ g₂ \ g₁, a i)
    (∑ i ∈ g₁ ∩ g₂, r i) (∑ i ∈ g₁ \ g₂, r i) (∑ i ∈ g₂ \ g₁, r i)
    (Finset.sum_nonneg fun i _ => (ha i).le) (Finset.sum_pos (fun i _ => ha i) hne1)
    (Finset.sum_pos (fun i _ => ha i) hne2) (Finset.sum_nonneg fun i _ => (hrho i).le)
    (Finset.sum_pos (fun i _ => hrho i) hne1) (Finset.sum_pos (fun i _ => hrho i) hne2)
    (by rw [← decU]; exact hRlt)
  rw [← decU a, ← decU r, ← dec1 a, ← dec1 r, ← dec2 a, ← dec2 r] at key
  have hS := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := fun i => r i * W i)
  linarith

open CoffmanMitrani in
theorem solution (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D)
    (g1 g2 : Finset (Fin D.M)) (hg1 : g1.Nonempty) (hg2 : g2.Nonempty)
    (ht1 : ∑ i ∈ g1, D.rho i * W i = D.loadBound g1)
    (ht2 : ∑ i ∈ g2, D.rho i * W i = D.loadBound g2) :
    g1 ⊆ g2 ∨ g2 ⊆ g1 := by
  have hpos : ∀ i, 0 < D.rho i := by
    intro i
    unfold Data.rho
    exact div_pos (D.lam_pos i) (D.mu_pos i)
  have hapos : ∀ i, 0 < D.rho i / D.mu i := fun i => div_pos (hpos i) (D.mu_pos i)
  obtain ⟨hc, hi⟩ := hW
  have hV : D.V = ∑ i, D.rho i / D.mu i := by
    unfold Data.V Data.rho
    apply Finset.sum_congr rfl
    intro i _
    rw [div_div, sq]
  have hlt : ∑ i, D.rho i < 1 := D.stable
  have hc' : ∑ i, D.rho i * W i = (∑ i, D.rho i / D.mu i) / (1 - ∑ i, D.rho i) := by
    rw [hc, hV]
  exact cm_5a81ea39_aux (fun i => D.rho i / D.mu i) D.rho W hapos hpos hlt hc'
    (fun g hg hgu => hi g hg hgu) g1 g2 hg1 ht1 ht2
