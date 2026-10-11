-- Prove2me | solution 1 for ComparativeAdvantage.relative_supply_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:07:01.138299+00:00
-- url     : https://prove2.me/submissions/98c8e088-34d1-402b-afb8-675cf98b214c

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

private theorem ca_cloth_only (c : Country) (PC PW : ℝ) (hPC : 0 < PC)
    (hPW : 0 < PW) (hp : c.aLC / c.aLW < PC / PW)
    (q : ℝ × ℝ) (hq : IsCompetitiveOutput c PC PW q) :
    q = (c.L / c.aLC, 0) := by
  have hcross : c.aLC * PW < PC * c.aLW :=
    (div_lt_div_iff₀ c.aLW_pos hPW).1 hp
  have hwage : PW / c.aLW < PC / c.aLC :=
    (div_lt_div_iff₀ c.aLW_pos c.aLC_pos).2 (by nlinarith)
  rcases hq with ⟨hx, hy, hbudget, hcloth, hwine⟩
  have hy0 : q.2 = 0 := by
    by_contra hn
    have hpos : 0 < q.2 := lt_of_le_of_ne hy (Ne.symm hn)
    exact (not_le_of_gt hwage) (hwine hpos)
  have hxval : q.1 = c.L / c.aLC := by
    apply (eq_div_iff (ne_of_gt c.aLC_pos)).2
    rw [hy0, mul_zero, add_zero] at hbudget
    nlinarith only [hbudget]
  exact Prod.ext hxval hy0

private theorem ca_wine_only (c : Country) (PC PW : ℝ) (hPC : 0 < PC)
    (hPW : 0 < PW) (hp : PC / PW < c.aLC / c.aLW)
    (q : ℝ × ℝ) (hq : IsCompetitiveOutput c PC PW q) :
    q = (0, c.L / c.aLW) := by
  have hcross : PC * c.aLW < c.aLC * PW :=
    (div_lt_div_iff₀ hPW c.aLW_pos).1 hp
  have hwage : PC / c.aLC < PW / c.aLW :=
    (div_lt_div_iff₀ c.aLC_pos c.aLW_pos).2 (by nlinarith)
  rcases hq with ⟨hx, hy, hbudget, hcloth, hwine⟩
  have hx0 : q.1 = 0 := by
    by_contra hn
    have hpos : 0 < q.1 := lt_of_le_of_ne hx (Ne.symm hn)
    exact (not_le_of_gt hwage) (hcloth hpos)
  have hyval : q.2 = c.L / c.aLW := by
    apply (eq_div_iff (ne_of_gt c.aLW_pos)).2
    rw [hx0, mul_zero, zero_add] at hbudget
    nlinarith only [hbudget]
  exact Prod.ext hx0 hyval

private theorem ca_tie_cloth (c : Country) (PC PW : ℝ) (hPC : 0 < PC)
    (hPW : 0 < PW) (hp : PC / PW = c.aLC / c.aLW)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (c.L / c.aLC)) :
    ∃ q : ℝ × ℝ, IsCompetitiveOutput c PC PW q ∧ q.1 = x := by
  rcases hx with ⟨hx0, hxmax⟩
  have hcross : PC * c.aLW = c.aLC * PW :=
    (div_eq_div_iff (ne_of_gt hPW) (ne_of_gt c.aLW_pos)).1 hp
  have hwage : PW / c.aLW = PC / c.aLC :=
    (div_eq_div_iff (ne_of_gt c.aLW_pos) (ne_of_gt c.aLC_pos)).2 (by nlinarith)
  have hmax : c.aLC * x ≤ c.L := by
    have hh := (le_div_iff₀ c.aLC_pos).1 hxmax
    nlinarith
  have hy0 : 0 ≤ (c.L - c.aLC * x) / c.aLW :=
    div_nonneg (by nlinarith) (le_of_lt c.aLW_pos)
  have hbudget :
      c.aLC * x + c.aLW * ((c.L - c.aLC * x) / c.aLW) = c.L := by
    field_simp [ne_of_gt c.aLW_pos] <;> ring
  refine ⟨(x, (c.L - c.aLC * x) / c.aLW), ?_, rfl⟩
  exact ⟨hx0, hy0, hbudget, (fun _ => le_of_eq hwage),
    (fun _ => le_of_eq hwage.symm)⟩

private theorem ca_tie_wine (c : Country) (PC PW : ℝ) (hPC : 0 < PC)
    (hPW : 0 < PW) (hp : PC / PW = c.aLC / c.aLW)
    (y : ℝ) (hy : y ∈ Set.Icc 0 (c.L / c.aLW)) :
    ∃ q : ℝ × ℝ, IsCompetitiveOutput c PC PW q ∧ q.2 = y := by
  rcases hy with ⟨hy0, hymax⟩
  have hcross : PC * c.aLW = c.aLC * PW :=
    (div_eq_div_iff (ne_of_gt hPW) (ne_of_gt c.aLW_pos)).1 hp
  have hwage : PW / c.aLW = PC / c.aLC :=
    (div_eq_div_iff (ne_of_gt c.aLW_pos) (ne_of_gt c.aLC_pos)).2 (by nlinarith)
  have hmax : c.aLW * y ≤ c.L := by
    have hh := (le_div_iff₀ c.aLW_pos).1 hymax
    nlinarith
  have hx0 : 0 ≤ (c.L - c.aLW * y) / c.aLC :=
    div_nonneg (by nlinarith) (le_of_lt c.aLC_pos)
  have hbudget :
      c.aLC * ((c.L - c.aLW * y) / c.aLC) + c.aLW * y = c.L := by
    field_simp [ne_of_gt c.aLC_pos] <;> ring
  refine ⟨((c.L - c.aLW * y) / c.aLC, y), ?_, rfl⟩
  exact ⟨hx0, hy0, hbudget, (fun _ => le_of_eq hwage),
    (fun _ => le_of_eq hwage.symm)⟩

theorem solution (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) :
    (PC / PW = h.aLC / h.aLW →
      (∀ qF, IsCompetitiveOutput f PC PW qF → qF = (0, f.L / f.aLW)) ∧
      ∀ x ∈ Set.Icc 0 (h.L / h.aLC), ∃ qH, IsCompetitiveOutput h PC PW qH ∧ qH.1 = x) ∧
    (PC / PW < h.aLC / h.aLW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH.1 + qF.1 = 0) ∧
    (h.aLC / h.aLW < PC / PW → PC / PW < f.aLC / f.aLW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH = (h.L / h.aLC, 0) ∧ qF = (0, f.L / f.aLW) ∧
        (qH.1 + qF.1) / (qH.2 + qF.2) = (h.L / h.aLC) / (f.L / f.aLW)) ∧
    (f.aLC / f.aLW < PC / PW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH.2 + qF.2 = 0) ∧
    (PC / PW = f.aLC / f.aLW →
      (∀ qH, IsCompetitiveOutput h PC PW qH → qH = (h.L / h.aLC, 0)) ∧
      ∀ y ∈ Set.Icc 0 (f.L / f.aLW), ∃ qF, IsCompetitiveOutput f PC PW qF ∧ qF.2 = y) := by
  change h.aLC / h.aLW < f.aLC / f.aLW at hCA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    constructor
    · intro qF hqF
      have hf : PC / PW < f.aLC / f.aLW := by rw [heq]; exact hCA
      exact ca_wine_only f PC PW hPC hPW hf qF hqF
    · intro x hx
      exact ca_tie_cloth h PC PW hPC hPW heq x hx
  · intro hp qH qF hqH hqF
    have hh : PC / PW < h.aLC / h.aLW := hp
    have hf : PC / PW < f.aLC / f.aLW := lt_trans hp hCA
    have hH := ca_wine_only h PC PW hPC hPW hh qH hqH
    have hF := ca_wine_only f PC PW hPC hPW hf qF hqF
    rw [hH, hF] <;> norm_num
  · intro hp hf qH qF hqH hqF
    have hH := ca_cloth_only h PC PW hPC hPW hp qH hqH
    have hF := ca_wine_only f PC PW hPC hPW hf qF hqF
    refine ⟨hH, hF, ?_⟩
    rw [hH, hF] <;> simp
  · intro hp qH qF hqH hqF
    have hh : h.aLC / h.aLW < PC / PW := lt_trans hCA hp
    have hH := ca_cloth_only h PC PW hPC hPW hh qH hqH
    have hF := ca_cloth_only f PC PW hPC hPW hp qF hqF
    rw [hH, hF] <;> norm_num
  · intro heq
    constructor
    · intro qH hqH
      have hh : h.aLC / h.aLW < PC / PW := by rw [heq]; exact hCA
      exact ca_cloth_only h PC PW hPC hPW hh qH hqH
    · intro y hy
      exact ca_tie_wine f PC PW hPC hPW heq y hy
