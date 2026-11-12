-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb36_L2_cauchy_eventwise_centred_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:51:52.734287+00:00
-- url     : https://prove2.me/submissions/de06c07e-afc6-49db-b136-4dbd79d38945

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

/-- Construct an event-centred L1 limit from a mean-vanishing L2 Cauchy grid. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 P)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (f nm.1 - f nm.2) 2 P) atTop (𝓝 (0 : ℝ≥0∞)))
    (hMean : Tendsto (fun n : ℕ => ∫ ω in A, f n ω ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∃ L : Ω → ℝ, Integrable L P ∧
      (∫ ω in A, L ω ∂P) = 0 ∧
      Tendsto (fun n : ℕ => ∫ ω in A, |L ω - f n ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 P := fun n => (hf n).toLp (f n)
  have hPair (n m : ℕ) :
      eLpNorm ((F n : Ω → ℝ) - (F m : Ω → ℝ)) 2 P =
        eLpNorm (f n - f m) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hf n).coeFn_toLp, (hf m).coeFn_toLp]
      with ω hn hm
    change F n ω - F m ω = f n ω - f m ω
    rw [hn, hm]
  have hF : CauchySeq F := by
    apply (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm F).2
    have heq : (fun nm : ℕ × ℕ =>
        eLpNorm ((F nm.1 : Ω → ℝ) - (F nm.2 : Ω → ℝ)) 2 P) =
        (fun nm : ℕ × ℕ => eLpNorm (f nm.1 - f nm.2) 2 P) := by
      funext nm
      exact hPair nm.1 nm.2
    rw [heq]
    exact hCauchy
  obtain ⟨L, hFL⟩ := cauchySeq_tendsto_of_complete hF
  have hLp : MemLp (L : Ω → ℝ) 2 P := Lp.memLp L
  have hLI : Integrable (L : Ω → ℝ) P := hLp.integrable (by norm_num)
  have hPairL (n : ℕ) :
      eLpNorm ((F n : Ω → ℝ) - (L : Ω → ℝ)) 2 P =
        eLpNorm (f n - (L : Ω → ℝ)) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with ω hn
    change F n ω - L ω = f n ω - L ω
    rw [hn]
  have hL2 : Tendsto (fun n =>
      eLpNorm (f n - (L : Ω → ℝ)) 2 P) atTop (𝓝 0) := by
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F L).mp hFL
    simpa only [hPairL] using ht
  have hEvent := avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
    P A f (L : Ω → ℝ) hf hLp hL2
  have hBound (n : ℕ) :
      |∫ ω in A, (L : Ω → ℝ) ω - f n ω ∂P| ≤
        ∫ ω in A, |(L : Ω → ℝ) ω - f n ω| ∂P := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := P.restrict A) (f := fun ω => (L : Ω → ℝ) ω - f n ω))
  have hNeg : Tendsto
      (fun n : ℕ => -(∫ ω in A,
        |(L : Ω → ℝ) ω - f n ω| ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using hEvent.neg
  have hDiff : Tendsto
      (fun n : ℕ => ∫ ω in A, (L : Ω → ℝ) ω - f n ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze hNeg hEvent
    · intro n
      exact (abs_le.mp (hBound n)).1
    · intro n
      exact (abs_le.mp (hBound n)).2
  have hI (n : ℕ) :
      (∫ ω in A, f n ω ∂P) =
        (∫ ω in A, (L : Ω → ℝ) ω ∂P) -
          (∫ ω in A, (L : Ω → ℝ) ω - f n ω ∂P) := by
    rw [integral_sub hLI.integrableOn (((hf n).integrable (by norm_num)).integrableOn)]
    ring
  have hLimit : Tendsto (fun n : ℕ => ∫ ω in A, f n ω ∂P)
      atTop (𝓝 (∫ ω in A, (L : Ω → ℝ) ω ∂P)) := by
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∫ ω in A, (L : Ω → ℝ) ω ∂P)
        atTop (𝓝 (∫ ω in A, (L : Ω → ℝ) ω ∂P))).sub hDiff
    simpa only [hI, sub_zero] using ht
  refine ⟨(L : Ω → ℝ), hLI, ?_, hEvent⟩
  exact tendsto_nhds_unique hLimit hMean
