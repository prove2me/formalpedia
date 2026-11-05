-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_sigmafinite_of_integrable_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:21:45.662851+00:00
-- url     : https://prove2.me/submissions/f5bb222e-306b-4725-b9a8-90dfab4528ea

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A positive a.e. integrable real function certifies sigma-finiteness
of its measure, by a countable cover of finite superlevel sets. -/
theorem solution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    SigmaFinite μ := by
  let bad : Set α := {x | f x ≤ 0}
  have hbad : μ bad = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hpos] with x hx
    exact not_le.mpr hx
  let band : ℕ → Set α :=
    fun n => {x | (1 : ℝ) / ((n : ℝ) + 1) ≤ f x}
  let S : Set (Set α) := range band ∪ {bad}
  have hc : S.Countable :=
    (countable_range band).union (countable_singleton bad)
  have hfinite : ∀ s ∈ S, μ s < ⊤ := by
    intro s hs
    rcases hs with ⟨n, rfl⟩ | hs
    · have hn : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      exact hf.measure_ge_lt_top hn
    · have heq : s = bad := mem_singleton_iff.mp hs
      rw [heq, hbad]
      exact ENNReal.zero_lt_top
  have hcover : ⋃₀ S = (univ : Set α) := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : f x ≤ 0
    · exact mem_sUnion.mpr ⟨bad, Or.inr rfl, hx⟩
    · have hxpos : 0 < f x := lt_of_not_ge hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hxpos
      exact mem_sUnion.mpr ⟨band n, Or.inl ⟨n, rfl⟩, hn.le⟩
  exact μ.sigmaFinite_of_countable hc hfinite hcover
