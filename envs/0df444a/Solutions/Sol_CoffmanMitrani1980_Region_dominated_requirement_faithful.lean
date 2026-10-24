-- Prove2me | solution 1 for CoffmanMitrani1980.Region.dominated_requirement_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:09:17.566801+00:00
-- url     : https://prove2.me/submissions/3291759f-3bcf-4269-b45a-83a9d4327ad9

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model
import Theorems.Thm_CoffmanMitrani1980_Region_conservation_polytope_eq_priority_hull


namespace CM87

lemma alg (aI aX aY s x y : ℝ) (haI : 0 ≤ aI) (haX : 0 < aX) (haY : 0 ≤ aY)
    (hx : 0 < x) (hy : 0 < y) (hs : 0 < s - x - y) :
    (aI + aX) / (s - x) + (aI + aY) / (s - y) < (aI + aX + aY) / (s - x - y) + aI / s := by
  have h1 : 0 < s - x := by linarith
  have h2 : 0 < s - y := by linarith
  have h3 : 0 < s := by linarith
  have P1 : 1 / (s - x) + 1 / (s - y) ≤ 1 / (s - x - y) + 1 / s := by
    rw [div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ hs.ne' h3.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hx hy, mul_pos (mul_pos hx hy) hs, mul_pos (mul_pos hx hy) h3,
      mul_pos (mul_pos hx hy) (add_pos hx hy)]
  have P2 : 1 / (s - x) < 1 / (s - x - y) := by
    apply one_div_lt_one_div_of_lt hs; linarith
  have P3 : 1 / (s - y) ≤ 1 / (s - x - y) := by
    apply one_div_le_one_div_of_le hs; linarith
  have e1 : (aI + aX) / (s - x) = aI * (1 / (s - x)) + aX * (1 / (s - x)) := by ring
  have e2 : (aI + aY) / (s - y) = aI * (1 / (s - y)) + aY * (1 / (s - y)) := by ring
  have e3 : (aI + aX + aY) / (s - x - y) = aI * (1 / (s - x - y)) + aX * (1 / (s - x - y)) +
      aY * (1 / (s - x - y)) := by ring
  have e4 : aI / s = aI * (1 / s) := by ring
  rw [e1, e2, e3, e4]
  have q1 := mul_le_mul_of_nonneg_left P1 haI
  have q2 := mul_lt_mul_of_pos_left P2 haX
  have q3 := mul_le_mul_of_nonneg_left P3 haY
  nlinarith

end CM87

open Finset CoffmanMitrani1980.Region

namespace CM87

variable {M : ℕ} (p : Params M)

lemma rho_pos (i : Fin M) : 0 < p.rho i := div_pos (p.lam_pos i) (p.mu_pos i)
lemma a_pos (i : Fin M) : 0 < p.a i := div_pos (rho_pos p i) (p.mu_pos i)

lemma sum_rho_lt (g : Finset (Fin M)) : ∑ i ∈ g, p.rho i < 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ g)
    (fun i _ _ => (rho_pos p i).le)
  exact lt_of_le_of_lt h p.load_lt_one

lemma f_empty : p.f ∅ = 0 := by simp [Params.f]

lemma supermod (A B : Finset (Fin M)) (hX : (A \ B).Nonempty) (hY : (B \ A).Nonempty) :
    p.f A + p.f B < p.f (A ∪ B) + p.f (A ∩ B) := by
  have sa1 := Finset.sum_inter_add_sum_sdiff A B p.a
  have sa2 := Finset.sum_inter_add_sum_sdiff B A p.a
  have sa3 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := p.a)
  have sr1 := Finset.sum_inter_add_sum_sdiff A B p.rho
  have sr2 := Finset.sum_inter_add_sum_sdiff B A p.rho
  have sr3 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := p.rho)
  rw [Finset.inter_comm B A] at sa2 sr2
  have haI : 0 ≤ ∑ i ∈ A ∩ B, p.a i := Finset.sum_nonneg (fun i _ => (a_pos p i).le)
  have haX : 0 < ∑ i ∈ A \ B, p.a i := Finset.sum_pos (fun i _ => a_pos p i) hX
  have haY : 0 ≤ ∑ i ∈ B \ A, p.a i := Finset.sum_nonneg (fun i _ => (a_pos p i).le)
  have hx : 0 < ∑ i ∈ A \ B, p.rho i := Finset.sum_pos (fun i _ => rho_pos p i) hX
  have hy : 0 < ∑ i ∈ B \ A, p.rho i := Finset.sum_pos (fun i _ => rho_pos p i) hY
  have hU := sum_rho_lt p (A ∪ B)
  have key := alg (∑ i ∈ A ∩ B, p.a i) (∑ i ∈ A \ B, p.a i) (∑ i ∈ B \ A, p.a i)
    (1 - ∑ i ∈ A ∩ B, p.rho i) (∑ i ∈ A \ B, p.rho i) (∑ i ∈ B \ A, p.rho i) haI haX haY hx hy
    (by linarith)
  simp only [Params.f]
  have e1 : ∑ i ∈ A, p.a i = ∑ i ∈ A ∩ B, p.a i + ∑ i ∈ A \ B, p.a i := sa1.symm
  have e2 : ∑ i ∈ B, p.a i = ∑ i ∈ A ∩ B, p.a i + ∑ i ∈ B \ A, p.a i := sa2.symm
  have e3 : ∑ i ∈ A ∪ B, p.a i =
      ∑ i ∈ A ∩ B, p.a i + ∑ i ∈ A \ B, p.a i + ∑ i ∈ B \ A, p.a i := by linarith
  have d1 : 1 - ∑ i ∈ A, p.rho i = (1 - ∑ i ∈ A ∩ B, p.rho i) - ∑ i ∈ A \ B, p.rho i := by
    linarith
  have d2 : 1 - ∑ i ∈ B, p.rho i = (1 - ∑ i ∈ A ∩ B, p.rho i) - ∑ i ∈ B \ A, p.rho i := by
    linarith
  have d3 : 1 - ∑ i ∈ A ∪ B, p.rho i =
      (1 - ∑ i ∈ A ∩ B, p.rho i) - ∑ i ∈ A \ B, p.rho i - ∑ i ∈ B \ A, p.rho i := by linarith
  rw [e1, e2, e3, d1, d2, d3]
  linarith

end CM87

theorem solution {M : ℕ} (hM : 0 < M) (p : Params M)
    (W : Fin M → ℝ)
    (hineq : ∀ g : Finset (Fin M), g.Nonempty → g ≠ univ → p.f g ≤ ∑ i ∈ g, p.rho i * W i)
    (hcons : p.V / (1 - ∑ i, p.rho i) < ∑ i, p.rho i * W i) :
    ∃ W' ∈ p.H, ∀ i, W' i ≤ W i := by
  have hfU : p.f univ = p.V / (1 - ∑ i, p.rho i) := by
    simp only [Params.f, Params.V]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Params.a, Params.rho]
    have := p.mu_pos i
    field_simp
  set D : Set (Fin M → ℝ) := (⋂ i, {W' : Fin M → ℝ | W' i ≤ W i}) ∩
    ⋂ (g : Finset (Fin M)) (_ : g.Nonempty), {W' | p.f g ≤ ∑ i ∈ g, p.rho i * W' i} with hD
  have memD : ∀ W', W' ∈ D ↔ (∀ i, W' i ≤ W i) ∧
      ∀ g : Finset (Fin M), g.Nonempty → p.f g ≤ ∑ i ∈ g, p.rho i * W' i := by
    intro W'; simp [hD, Set.mem_iInter]
  have hWD : W ∈ D := by
    rw [memD]
    refine ⟨fun i => le_rfl, fun g hg => ?_⟩
    by_cases hgu : g = univ
    · subst hgu; rw [hfU]; exact hcons.le
    · exact hineq g hg hgu
  have hDclosed : IsClosed D := by
    apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
    · exact isClosed_iInter fun g => isClosed_iInter fun _ =>
        isClosed_le continuous_const (by fun_prop)
  set lo : Fin M → ℝ := fun i => p.f {i} / p.rho i with hlo
  have hDsub : D ⊆ Set.Icc lo W := by
    intro W' hW'
    rw [memD] at hW'
    refine ⟨fun i => ?_, hW'.1⟩
    have h := hW'.2 {i} (singleton_nonempty i)
    simp only [sum_singleton] at h
    simp only [hlo]
    rw [div_le_iff₀ (CM87.rho_pos p i)]
    linarith
  have hDcpt : IsCompact D := isCompact_Icc.of_isClosed_subset hDclosed hDsub
  obtain ⟨Ws, hWsD, hmin⟩ := hDcpt.exists_isMinOn ⟨W, hWD⟩
    (show Continuous (fun W' : Fin M → ℝ => ∑ i, p.rho i * W' i) by fun_prop).continuousOn
  rw [memD] at hWsD
  obtain ⟨hWsW, hWsg⟩ := hWsD
  -- conservation at the minimizer
  have hconsWs : ∑ i, p.rho i * Ws i = p.V / (1 - ∑ i, p.rho i) := by
    by_contra hne
    have hgt : p.f univ < ∑ i, p.rho i * Ws i := by
      rw [hfU]
      have := hWsg univ (univ_nonempty_iff.2 ⟨⟨0, hM⟩⟩)
      rw [hfU] at this
      exact lt_of_le_of_ne this (Ne.symm hne)
    -- every class lies in a tight set
    have htight : ∀ i, ∃ g : Finset (Fin M), i ∈ g ∧ ∑ j ∈ g, p.rho j * Ws j = p.f g := by
      intro i
      by_contra hno
      push Not at hno
      obtain ⟨g0, hg0, hg0min⟩ := Finset.exists_min_image (univ.filter (fun g : Finset (Fin M) => i ∈ g))
        (fun g => ∑ j ∈ g, p.rho j * Ws j - p.f g) ⟨{i}, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hg0
      set δ := ∑ j ∈ g0, p.rho j * Ws j - p.f g0 with hδ
      have hδpos : 0 < δ := by
        have h1 := hWsg g0 ⟨i, hg0⟩
        have h2 := hno g0 hg0
        rw [hδ]; exact sub_pos.2 (lt_of_le_of_ne h1 (Ne.symm h2))
      have hρi := CM87.rho_pos p i
      set ε := δ / (2 * p.rho i) with hε
      have hεpos : 0 < ε := by positivity
      set W' : Fin M → ℝ := Ws - ε • Pi.single i 1 with hW'
      have hsum : ∀ g : Finset (Fin M), ∑ j ∈ g, p.rho j * W' j =
          ∑ j ∈ g, p.rho j * Ws j - (if i ∈ g then p.rho i * ε else 0) := by
        intro g
        simp only [hW', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_sub,
          Finset.sum_sub_distrib]
        congr 1
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      have hW'D : W' ∈ D := by
        rw [memD]
        refine ⟨fun j => ?_, fun g hg => ?_⟩
        · have : W' j ≤ Ws j := by
            simp only [hW', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs <;> nlinarith
          exact this.trans (hWsW j)
        · rw [hsum g]
          by_cases hig : i ∈ g
          · rw [if_pos hig]
            have hm := hg0min g (by simp [hig])
            have : p.rho i * ε = δ / 2 := by rw [hε]; field_simp
            rw [this]; linarith
          · rw [if_neg hig]; simp only [sub_zero]; exact hWsg g hg
      have hlt : ∑ j, p.rho j * W' j < ∑ j, p.rho j * Ws j := by
        rw [hsum univ, if_pos (mem_univ i)]
        have := mul_pos hρi hεpos
        linarith
      have := hmin hW'D
      simp only [Set.mem_ofPred_eq] at this
      linarith
    choose g hgi hgt using htight
    have hproper : ∀ i, g i ≠ univ := by
      intro i h
      have := hgt i
      rw [h] at this
      linarith
    have hchain : ∀ i j, g i ⊆ g j ∨ g j ⊆ g i := by
      intro i j
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have hX : (g i \ g j).Nonempty := Finset.sdiff_nonempty.2 h1
      have hY : (g j \ g i).Nonempty := Finset.sdiff_nonempty.2 h2
      have hs := CM87.supermod p (g i) (g j) hX hY
      have hU := hWsg (g i ∪ g j) ⟨i, mem_union_left _ (hgi i)⟩
      have hI : p.f (g i ∩ g j) ≤ ∑ k ∈ g i ∩ g j, p.rho k * Ws k := by
        rcases (g i ∩ g j).eq_empty_or_nonempty with h | h
        · rw [h, CM87.f_empty]; simp
        · exact hWsg _ h
      have hsplit := Finset.sum_union_inter (s₁ := g i) (s₂ := g j) (f := fun k => p.rho k * Ws k)
      have t1 := hgt i
      have t2 := hgt j
      linarith
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image univ (fun i => (g i).card)
      (univ_nonempty_iff.2 ⟨⟨0, hM⟩⟩)
    apply hproper i0
    apply Finset.eq_univ_of_forall
    intro j
    rcases hchain j i0 with h | h
    · exact h (hgi j)
    · have hc := hi0 j (mem_univ j)
      have : g i0 = g j := Finset.eq_of_subset_of_card_le h hc
      rw [this]; exact hgi j
  have hHss : Ws ∈ p.Hss := ⟨hconsWs, fun g hg _ => hWsg g hg⟩
  rw [conservation_polytope_eq_priority_hull hM p] at hHss
  exact ⟨Ws, hHss, hWsW⟩
