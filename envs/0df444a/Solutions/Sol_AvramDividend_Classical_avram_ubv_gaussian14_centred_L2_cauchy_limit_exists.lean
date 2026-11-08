-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian14_centred_L2_cauchy_limit_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:29:38.851731+00:00
-- url     : https://prove2.me/submissions/a8a7d084-7aa1-48b7-b78b-2445af86f4f2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Centred L² stochastic grids have a genuinely centred L² terminal limit
when their pairwise L² distances tend to zero; the limit is constructed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ)
    (hQ2 : ∀ n, MemLp (Q n) 2 P)
    (hQzero : ∀ n, (∫ ω, Q n ω ∂P) = 0)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (Q nm.1 - Q nm.2) 2 P) atTop (𝓝 0)) :
    ∃ L : Ω → ℝ, MemLp L 2 P ∧
      (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 P := fun n => (hQ2 n).toLp (Q n)
  have hPair (n m : ℕ) :
      eLpNorm ((F n : Ω → ℝ) - (F m : Ω → ℝ)) 2 P =
        eLpNorm (Q n - Q m) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hQ2 n).coeFn_toLp, (hQ2 m).coeFn_toLp]
      with ω hn hm
    change F n ω - F m ω = Q n ω - Q m ω
    rw [hn, hm]
  have hF : CauchySeq F := by
    apply (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm F).2
    have hfun : (fun nm : ℕ × ℕ =>
        eLpNorm ((F nm.1 : Ω → ℝ) - (F nm.2 : Ω → ℝ)) 2 P) =
        (fun nm : ℕ × ℕ => eLpNorm (Q nm.1 - Q nm.2) 2 P) := by
      funext nm
      exact hPair nm.1 nm.2
    rw [hfun]
    exact hCauchy
  obtain ⟨L, hFL⟩ := cauchySeq_tendsto_of_complete hF
  have hLp : MemLp (L : Ω → ℝ) 2 P := Lp.memLp L
  have hPairL (n : ℕ) :
      eLpNorm ((F n : Ω → ℝ) - (L : Ω → ℝ)) 2 P =
        eLpNorm (Q n - (L : Ω → ℝ)) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hQ2 n).coeFn_toLp] with ω hn
    change F n ω - L ω = Q n ω - L ω
    rw [hn]
  have hL2 : Tendsto (fun n =>
      eLpNorm (Q n - (L : Ω → ℝ)) 2 P) atTop (𝓝 0) := by
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F L).mp hFL
    simpa only [hPairL] using ht
  have hBound (n : ℕ) :
      eLpNorm (Q n - (L : Ω → ℝ)) 1 P ≤
        eLpNorm (Q n - (L : Ω → ℝ)) 2 P :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hQ2 n).aestronglyMeasurable.sub hLp.aestronglyMeasurable)
  have hL1 : Tendsto (fun n =>
      eLpNorm (Q n - (L : Ω → ℝ)) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
      (fun _ => zero_le) hBound
  have hInt := tendsto_integral_of_L1' (L : Ω → ℝ)
    hLp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => (hQ2 n).integrable (by norm_num))) hL1
  refine ⟨(L : Ω → ℝ), hLp, ?_, hL2⟩
  exact tendsto_nhds_unique hInt (by
    simpa only [hQzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
