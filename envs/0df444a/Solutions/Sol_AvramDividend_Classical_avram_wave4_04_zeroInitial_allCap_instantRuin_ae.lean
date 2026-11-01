-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_zeroInitial_allCap_instantRuin_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:38:41.566087+00:00
-- url     : https://prove2.me/submissions/31f0faad-c1ee-4a8d-91cf-5a7a46be47de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At zero initial reserve, every nondecreasing admissible dividend control
inherits the source's instantaneous strict downward crossing in UBV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by
  filter_upwards [ae_negative_near_zero_of_unbounded_variation X hBV] with ω hnear
  have hD_nonneg : ∀ t : ℝ≥0, 0 ≤ D t ω := by
    intro t
    have ht := hD.1.1.2.1 ω (bot_le : (0 : ℝ≥0) ≤ t)
    simpa [hD.1.1.1 ω] using ht
  have hτ_le (ε : ℝ≥0) (hε : 0 < ε) :
      ruinTime X 0 D ω ≤ (ε : ℝ≥0∞) := by
    obtain ⟨s, hs, hXs⟩ := hnear ε hε
    have hneg : riskProcess X 0 D s ω < 0 := by
      dsimp [riskProcess]
      linarith [hD_nonneg s]
    have hruin_s : ruinTime X 0 D ω ≤ (s : ℝ≥0∞) := by
      unfold ruinTime
      exact iInf_le_of_le s
        (iInf_le (fun _ : riskProcess X 0 D s ω < 0 => (s : ℝ≥0∞)) hneg)
    exact hruin_s.trans (ENNReal.coe_le_coe.mpr hs.le)
  let τ := ruinTime X 0 D ω
  have hτfinite : τ ≠ ⊤ := by
    intro ht
    have hbound : τ ≤ (1 : ℝ≥0∞) := hτ_le 1 (by norm_num)
    simp [ht] at hbound
  have hτeq : (τ.toNNReal : ℝ≥0∞) = τ :=
    ENNReal.coe_toNNReal hτfinite
  by_contra hzero
  have hnnnonzero : τ.toNNReal ≠ 0 := by
    intro hz
    apply hzero
    calc
      τ = (τ.toNNReal : ℝ≥0∞) := hτeq.symm
      _ = 0 := by simp [hz]
  have hpositive : 0 < τ.toNNReal := pos_iff_ne_zero.mpr hnnnonzero
  let ε : ℝ≥0 := τ.toNNReal / 2
  have hε : 0 < ε := by
    dsimp [ε]
    exact half_pos hpositive
  have hbound : τ ≤ (ε : ℝ≥0∞) := hτ_le ε hε
  have hhalf : ε < τ.toNNReal := by
    dsimp [ε]
    exact half_lt_self hpositive
  have hstrict : (ε : ℝ≥0∞) < τ := by
    rw [← hτeq]
    exact ENNReal.coe_lt_coe.mpr hhalf
  exact (not_lt_of_ge hbound) hstrict
