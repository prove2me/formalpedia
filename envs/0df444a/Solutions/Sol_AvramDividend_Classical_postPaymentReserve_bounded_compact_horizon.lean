-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_bounded_compact_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:32:28.142199+00:00
-- url     : https://prove2.me/submissions/6069619a-0638-46a3-9378-5b5e5d461488

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    Bornology.IsBounded
      ((fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) ''
        Set.Icc (0 : ℝ≥0) T) := by
  let f : ℝ≥0 → ℝ :=
    fun t => x + X.X t ω - rightLimit D t ω
  obtain ⟨hcont, hleft, _⟩ :=
    postPaymentReserve_cadlag_adapted X x D hD
  have hr (t : ℝ≥0) :
      Tendsto f (𝓝[≥] t) (𝓝 (f t)) :=
    (hcont ω t).tendsto
  have hl (t : ℝ≥0) :
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) := by
    by_cases ht : t = 0
    · subst t
      refine ⟨0, ?_⟩
      have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
        nhdsLT_eq_bot_iff.mpr
          (.inl (fun v => (zero_le : (0 : ℝ≥0) ≤ v)))
      rw [hb]
      exact tendsto_bot
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
      exact hleft ω t htpos
  have hrneg (t : ℝ≥0) :
      Tendsto (fun s => -f s) (𝓝[≥] t) (𝓝 (-f t)) :=
    (hr t).neg
  have hlneg (t : ℝ≥0) :
      ∃ l : ℝ, Tendsto (fun s => -f s) (𝓝[<] t) (𝓝 l) := by
    obtain ⟨l, hlim⟩ := hl t
    exact ⟨-l, hlim.neg⟩
  have ha0 : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) T => f s.1)) :=
    one_sided_limits_bddAbove_Icc f hr hl T
  have hb0 : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) T => -f s.1)) :=
    one_sided_limits_bddAbove_Icc (fun s => -f s) hrneg hlneg T
  have ha : BddAbove (f '' Set.Icc (0 : ℝ≥0) T) := by
    obtain ⟨A, hA⟩ := ha0
    refine ⟨A, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact hA ⟨⟨s, hs⟩, rfl⟩
  have hb : BddBelow (f '' Set.Icc (0 : ℝ≥0) T) := by
    obtain ⟨B, hB⟩ := hb0
    refine ⟨-B, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have hz : -f s ≤ B := hB ⟨⟨s, hs⟩, rfl⟩
    linarith
  exact hb.isBounded ha
