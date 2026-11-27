-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_nested_cash_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:10:21.562176+00:00
-- url     : https://prove2.me/submissions/4041d370-4b0d-4042-a818-7c3126ce64c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) (θ : ℕ → Ω → ℝ≥0)
    (hθle : ∀ k ω, θ k ω ≤ T.toNNReal)
    (hmono : ∀ ω, Monotone (fun k => θ k ω))
    (hcover : ∀ᵐ ω ∂P, ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∃ k, t ≤ (θ k ω : ℝ)) :
    ∀ᵐ ω ∂P, Tendsto (fun k =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by 
  filter_upwards [hcover] with ω hcov
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let S : ℕ → Set ℝ := fun k => paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ)
  let U : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T
  have hS (k : ℕ) : MeasurableSet (S k) := by
    dsimp [S, paymentTimes]
    measurability
  have hU : MeasurableSet U := by
    dsimp [U, paymentTimes]
    measurability
  have hsub (k : ℕ) : S k ⊆ U := by
    intro t ht
    have h : (θ k ω : ℝ) ≤ (T.toNNReal : ℝ) := by exact_mod_cast hθle k ω
    rw [Real.coe_toNNReal T hT] at h
    exact ⟨ht.1, le_trans (show t ≤ (θ k ω : ℝ) from ht.2) h⟩
  have hm : Monotone S := by
    intro i j hij t ht
    have h : (θ i ω : ℝ) ≤ (θ j ω : ℝ) := by exact_mod_cast hmono ω hij
    exact ⟨ht.1, le_trans (show t ≤ (θ i ω : ℝ) from ht.2) h⟩
  have hcov' : U ⊆ ⋃ k : ℕ, (∅ : Set ℝ) ∪ S k := by
    intro t ht
    obtain ⟨k, hk⟩ := hcov t ht
    exact mem_iUnion.mpr ⟨k, Or.inr ⟨ht.1, hk⟩⟩
  have hsup : (∫⁻ t in U, f t ∂dividendMeasure D ω) =
      ⨆ k, ∫⁻ t in S k, f t ∂dividendMeasure D ω := by
    apply le_antisymm
    · simpa only [empty_union] using
        avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
          X q x T D ω ∅ S MeasurableSet.empty hS hm hcov'
    · exact iSup_le (fun k => lintegral_mono_set (hsub k))
  have hmonoCash : Monotone (fun k => ∫⁻ t in S k, f t ∂dividendMeasure D ω) :=
    fun i j hij => lintegral_mono_set (hm hij)
  change Tendsto (fun k => ∫⁻ t in S k, f t ∂dividendMeasure D ω)
    atTop (𝓝 (∫⁻ t in U, f t ∂dividendMeasure D ω))
  rw [hsup]
  exact tendsto_atTop_iSup hmonoCash
