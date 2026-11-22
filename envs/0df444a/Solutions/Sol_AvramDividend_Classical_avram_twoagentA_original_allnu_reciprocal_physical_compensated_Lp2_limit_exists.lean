-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:45:24.389823+00:00
-- url     : https://prove2.me/submissions/89d60a89-39ea-46a1-a604-5003f0ff2d5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∃ M : ℕ → Lp ℝ 2 P,
      (∀ n, (M n : Ω → ℝ) =ᵐ[P] F n) ∧
        ∃ L : Lp ℝ 2 P, Tendsto M atTop (𝓝 L) := by
  classical
  intro B NX r F
  have hMem (n : ℕ) : MemLp (F n) (2 : ℝ≥0∞) P := by
    have h := (avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
      X T 0 n (Nat.zero_le n)).2
    simpa only [F, Finset.range_eq_Ico] using h
  have hRaw : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, N ≤ m →
        Integrable (fun ω => (F n ω - F m ω) ^ 2) P ∧
          (∫ ω, (F n ω - F m ω) ^ 2 ∂P) < ε := by
    simpa only [] using
      (avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy X T)
  have hEnergy : Tendsto
      (fun nm : ℕ × ℕ => ∫ ω, (F nm.1 ω - F nm.2 ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [] with nm
      exact lt_of_lt_of_le ha (integral_nonneg (fun ω => sq_nonneg _))
    · intro a ha
      obtain ⟨N, hN⟩ := hRaw a ha
      filter_upwards [Filter.eventually_ge_atTop (N, N)] with nm hnm
      exact (hN nm.1 hnm.1 nm.2 hnm.2).2
  have hNorm : Tendsto
      (fun nm : ℕ × ℕ => eLpNorm (F nm.1 - F nm.2) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
      P F (fun n m => (hMem n).sub (hMem m)) hEnergy
  let M : ℕ → Lp ℝ 2 P := fun n => (hMem n).toLp (F n)
  have hEq (n m : ℕ) :
      eLpNorm ((M n : Ω → ℝ) - (M m : Ω → ℝ)) 2 P =
        eLpNorm (F n - F m) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hMem n).coeFn_toLp, (hMem m).coeFn_toLp]
      with ω hn hm
    change M n ω - M m ω = F n ω - F m ω
    rw [hn, hm]
  have hCauchy : CauchySeq M := by
    apply (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm M).2
    have hFun :
        (fun nm : ℕ × ℕ =>
          eLpNorm ((M nm.1 : Ω → ℝ) - (M nm.2 : Ω → ℝ)) 2 P) =
        (fun nm : ℕ × ℕ => eLpNorm (F nm.1 - F nm.2) 2 P) := by
      funext nm
      exact hEq nm.1 nm.2
    rw [hFun]
    exact hNorm
  obtain ⟨L, hLimit⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨M, ?_, L, hLimit⟩
  intro n
  exact (hMem n).coeFn_toLp
