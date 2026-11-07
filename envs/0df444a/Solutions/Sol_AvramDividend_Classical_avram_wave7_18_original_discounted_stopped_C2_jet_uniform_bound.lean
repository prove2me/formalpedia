-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:37:09.579363+00:00
-- url     : https://prove2.me/submissions/539617f8-5052-486b-a2cf-4bddb7c5c510

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ (s : ℝ≥0), s < T →
          |Real.exp (-(q * (s : ℝ))) *
             w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |Real.exp (-(q * (s : ℝ))) *
             deriv w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |Real.exp (-(q * (s : ℝ))) *
             deriv (deriv w) (x + X.X s ω - rightLimit D s ω)| ≤ M := by
  obtain ⟨M, hM, hjet⟩ :=
    avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound
      X x D hD C w hw r lower upper hlower hlu hcap hdense B
  refine ⟨M, hM, ?_⟩
  intro ω T hT s hs
  obtain ⟨h0, h1, h2⟩ := hjet ω T hT s hs
  have hnonneg : 0 ≤ (s : ℝ) := NNReal.coe_nonneg s
  have he0 : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have he1 : Real.exp (-(q * (s : ℝ))) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr
      (mul_nonneg (le_of_lt hq) hnonneg))
  have hbound (v : ℝ) (hv : |v| ≤ M) :
      |Real.exp (-(q * (s : ℝ))) * v| ≤ M := by
    rw [abs_mul, abs_of_nonneg he0]
    calc
      Real.exp (-(q * (s : ℝ))) * |v| ≤
          Real.exp (-(q * (s : ℝ))) * M :=
        mul_le_mul_of_nonneg_left hv he0
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right he1 hM
      _ = M := one_mul M
  exact ⟨hbound _ h0, hbound _ h1, hbound _ h2⟩
