-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_le_of_strict_terminal_positive_truncations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:14:05.220984+00:00
-- url     : https://prove2.me/submissions/0e1a3c40-d585-4061-9770-ba1a87cfdbf9

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) (T : ℝ) (hT : 0 < T)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hST : ∀ r ∈ S, r < T)
    (hzero : (μ.restrict S) (Set.Iic (0 : ℝ)) = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (B : ℝ≥0∞)
    (hbound : ∀ t : ℝ, 0 ≤ t → t < T →
      (∫⁻ r in S, if r ∈ Set.Ioc (0 : ℝ) t then f r else 0 ∂μ) ≤ B) :
    (∫⁻ r in S, f r ∂μ) ≤ B := by
  let I := {q : ℚ // (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < T}
  let g : I → ℝ → ℝ≥0∞ := fun q r =>
    if r ∈ Set.Ioc (0 : ℝ) (q.1 : ℝ) then f r else 0
  have hmeas : ∀ q : I, Measurable (g q) := by
    intro q
    exact Measurable.ite measurableSet_Ioc hf measurable_const
  have hmono (a b : I) (hab : a.1 ≤ b.1) : g a ≤ g b := by
    intro r
    change (if r ∈ Set.Ioc (0 : ℝ) (a.1 : ℝ) then f r else 0) ≤
      (if r ∈ Set.Ioc (0 : ℝ) (b.1 : ℝ) then f r else 0)
    by_cases ha : r ∈ Set.Ioc (0 : ℝ) (a.1 : ℝ)
    · have hrat : (a.1 : ℝ) ≤ (b.1 : ℝ) := by exact_mod_cast hab
      have hb : r ∈ Set.Ioc (0 : ℝ) (b.1 : ℝ) :=
        ⟨ha.1, ha.2.trans hrat⟩
      simp only [if_pos ha, if_pos hb, le_refl]
    · simp only [if_neg ha]
      exact zero_le
  have hdir : Directed (fun f g : ℝ → ℝ≥0∞ => f ≤ g) g := by
    intro a b
    rcases le_total a.1 b.1 with hab | hba
    · exact ⟨b, hmono a b hab, le_rfl⟩
    · exact ⟨a, le_rfl, hmono b a hba⟩
  have hsup (r : ℝ) (hrpos : 0 < r) (hrS : r ∈ S) :
      (⨆ q : I, g q r) = f r := by
    apply le_antisymm
    · apply iSup_le
      intro q
      dsimp [g]
      split_ifs
      · exact le_refl _
      · exact zero_le
    · obtain ⟨q, hqr, hqT⟩ := exists_rat_btwn (hST r hrS)
      let a : I := ⟨q, le_of_lt (hrpos.trans hqr), hqT⟩
      have hmem : r ∈ Set.Ioc (0 : ℝ) (a.1 : ℝ) :=
        ⟨hrpos, le_of_lt hqr⟩
      calc
        f r = g a r := by
          dsimp [g]
          rw [if_pos hmem]
        _ ≤ ⨆ q : I, g q r := le_iSup_of_le a le_rfl
  have hae : ∀ᵐ r ∂(μ.restrict S), r ∉ Set.Iic (0 : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have heq : (∫⁻ r in S, f r ∂μ) =
      (∫⁻ r in S, ⨆ q : I, g q r ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hS, hae] with r hrS hr
    exact (hsup r (lt_of_not_ge hr) hrS).symm
  calc
    (∫⁻ r in S, f r ∂μ) =
        ∫⁻ r in S, ⨆ q : I, g q r ∂μ := heq
    _ = ⨆ q : I, ∫⁻ r in S, g q r ∂μ :=
      lintegral_iSup_directed_of_measurable hmeas hdir
    _ ≤ B := by
      apply iSup_le
      intro q
      exact hbound (q.1 : ℝ) q.property.1 q.property.2
