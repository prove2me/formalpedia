-- Prove2me | solution 1 for ConitzerFPPE.Core.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T10:51:29.642502+00:00
-- url     : https://prove2.me/submissions/de24e361-8a00-4720-9655-32dc063c00a2

import Definitions.Def_ConitzerFPPE_Core_IsParetoDominant
import Definitions.Def_ConitzerFPPE_Core_IsFPPE
import Definitions.Def_ConitzerFPPE_Core_UnnecessarilyPaced

open ConitzerFPPE.Core

noncomputable def cGame : MultPacing.Existence.PacingGame (Fin 2) (Fin 1) where
  v i _ := if i = 0 then 2 else 1
  B i := if i = 0 then 1 else 2
  v_nonneg i _ := by split_ifs <;> norm_num
  B_pos i := by split_ifs <;> norm_num

noncomputable def cAlpha : Fin 2 → ℝ := fun i => if i = 0 then (1 / 2 : ℝ) else 1

def cAlloc : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 0 else 1

private lemma price_cAlpha : price cGame cAlpha 0 = 1 := by
  unfold price
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro k _
    cases k with
    | none => norm_num
    | some i =>
      fin_cases i <;> simp [cGame, cAlpha]
  · have hmem : (some (1 : Fin 2) : Option (Fin 2)) ∈ (Finset.univ : Finset (Option (Fin 2))) :=
      Finset.mem_univ _
    have hle := Finset.le_sup'
      (f := fun k : Option (Fin 2) => match k with | none => (0 : ℝ) | some i => cAlpha i * cGame.v i 0)
      hmem
    have hval : (match (some (1 : Fin 2) : Option (Fin 2)) with
        | none => (0 : ℝ)
        | some i => cAlpha i * cGame.v i 0) = 1 := by
      simp [cGame, cAlpha]
    rw [hval] at hle
    exact hle

private lemma isBFPM_c : IsBFPM cGame cAlpha cAlloc where
  multiplier_bounds i := by
    fin_cases i <;> simp [cAlpha, Set.mem_Icc] <;> norm_num
  allocation_bounds i j := by
    fin_cases i <;> fin_cases j <;> simp [cAlloc, Set.mem_Icc]
  highest_bidder i j hpos := by
    fin_cases j
    fin_cases i
    · simp [cAlloc] at hpos
    · change cAlpha 1 * cGame.v 1 0 = price cGame cAlpha 0
      rw [price_cAlpha]
      simp [cAlpha, cGame]
  budget_feasible i := by
    fin_cases i
    · change spend cGame cAlpha cAlloc 0 ≤ cGame.B 0
      rw [spend, Fin.sum_univ_one, price_cAlpha]
      simp [cAlloc, cGame]
    · change spend cGame cAlpha cAlloc 1 ≤ cGame.B 1
      rw [spend, Fin.sum_univ_one, price_cAlpha]
      simp [cAlloc, cGame]
  positive_price_clearance j _ := by
    fin_cases j
    simp [Fin.sum_univ_two, cAlloc]
  no_overselling j := by
    fin_cases j
    simp [Fin.sum_univ_two, cAlloc]

private lemma isParetoDominant_c : IsParetoDominant cGame cAlpha cAlloc := by
  refine ⟨isBFPM_c, ?_⟩
  intro β y hβ i
  fin_cases i
  · change β 0 ≤ cAlpha 0
    simp only [cAlpha, ↓reduceIte]
    by_contra hlt
    rw [not_le] at hlt
    have hmem0 : (some (0 : Fin 2) : Option (Fin 2)) ∈ (Finset.univ : Finset (Option (Fin 2))) :=
      Finset.mem_univ _
    have hp0 : β 0 * cGame.v 0 0 ≤ price cGame β 0 := by
      unfold price
      exact Finset.le_sup'
        (f := fun k : Option (Fin 2) => match k with | none => (0 : ℝ) | some i => β i * cGame.v i 0)
        hmem0
    have hv0 : cGame.v 0 0 = 2 := rfl
    rw [hv0] at hp0
    have hp_gt_one : 1 < price cGame β 0 := by linarith
    have hp_pos : 0 < price cGame β 0 := by linarith
    have hβ1_le : β 1 ≤ 1 := (hβ.multiplier_bounds 1).2
    have hy1_nonneg : 0 ≤ y 1 0 := (hβ.allocation_bounds 1 0).1
    have hy1_zero : y 1 0 = 0 := by
      by_contra hy1_ne
      have hy1_pos : 0 < y 1 0 := lt_of_le_of_ne hy1_nonneg (Ne.symm hy1_ne)
      have htop1 := hβ.highest_bidder 1 0 hy1_pos
      have hv1 : cGame.v 1 0 = 1 := rfl
      rw [hv1, mul_one] at htop1
      linarith
    have hsum : y 0 0 + y 1 0 = 1 := by
      have hclr := hβ.positive_price_clearance 0 hp_pos
      simpa [Fin.sum_univ_two] using hclr
    have hy0_one : y 0 0 = 1 := by linarith
    have hbud0 : spend cGame β y 0 ≤ cGame.B 0 := hβ.budget_feasible 0
    have hspend0 : spend cGame β y 0 = price cGame β 0 := by
      simp [spend, hy0_one]
    have hB0 : cGame.B 0 = 1 := rfl
    linarith
  · change β 1 ≤ cAlpha 1
    have h1 : cAlpha 1 = 1 := by simp [cAlpha]
    rw [h1]
    exact (hβ.multiplier_bounds 1).2

theorem solution :
    ¬ (∀ {N M : Type} [Fintype N] [Fintype M]
      (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ)
      (_hmax : IsParetoDominant P α x),
      (∀ i, ¬ UnnecessarilyPaced P α x i) ∧ IsFPPE P α x) := by
  intro h
  have h0 := (h cGame cAlpha cAlloc isParetoDominant_c).1 0
  apply h0
  refine ⟨?_, ?_⟩
  · simp [spend, cAlloc, cGame]
  · simp [cAlpha]
    norm_num
