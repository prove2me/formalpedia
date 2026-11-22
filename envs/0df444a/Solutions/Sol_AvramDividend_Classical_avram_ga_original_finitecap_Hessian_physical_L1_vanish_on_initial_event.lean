-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_Hessian_physical_L1_vanish_on_initial_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:29:03.270889+00:00
-- url     : https://prove2.me/submissions/a2a1450e-be44-4601-a5f8-58a973b6fdf6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_physical_Hessian_second_chaos_expected_absolute_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_abs_L1_global_to_restricted
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H U : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ (m i : ℕ), i < m + 1 →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2)) ^ 2) P)
    (hUeq : ∀ (m i : ℕ) (ω : Ω),
      U m i ω =
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    (hULp : ∀ m i, MemLp (U m i) 2 P)
    (hUadapt : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      StronglyMeasurable[𝓕.rightCont (((i + 1 : ℕ) : ℝ≥0) * Δ)] (U m i))
    (hUcenter : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      P[U m i | 𝓕.rightCont ((i : ℝ≥0) * Δ)] =ᵐ[P]
        (fun _ => (0 : ℝ)))
    (A : Set Ω) :
    Tendsto
      (fun m : ℕ => ∫ ω in A,
        |∑ i ∈ Finset.range (m + 1), U m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let Q : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range (m + 1), U m i ω
  have hQLp (m : ℕ) : MemLp (Q m) 2 P :=
    memLp_finset_sum (Finset.range (m + 1))
      (by intro i hi; exact hULp m i)
  have hAbs (m : ℕ) : Integrable (fun ω => |Q m ω|) P := by
    have hInt : Integrable (Q m) P :=
      (hQLp m).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact hInt.abs
  have hGlobal :=
    avram_ga_original_physical_Hessian_second_chaos_expected_absolute_L1_vanish
      X hX hν n hn H U K hK hH hHI hUeq hULp hUadapt hUcenter
  exact (avram_ga_abs_L1_global_to_restricted P A Q hAbs
    (by simpa only [Q] using hGlobal)).2
