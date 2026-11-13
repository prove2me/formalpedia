-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_centered_covariance_zero_from_additive_variances
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:01:11.321111+00:00
-- url     : https://prove2.me/submissions/6b0d4726-8fe3-4370-972f-5d51b518de18

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B U : Ω → ℝ) (rA rB : ℝ)
    (hA : Integrable (fun ω => (A ω) ^ 2) P)
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hU : Integrable (fun ω => (U ω) ^ 2) P)
    (hAdd : ∀ᵐ ω ∂P, U ω = A ω + B ω)
    (hMeanA : (∫ ω, (A ω) ^ 2 ∂P) = rA)
    (hMeanB : (∫ ω, (B ω) ^ 2 ∂P) = rB)
    (hMeanU : (∫ ω, (U ω) ^ 2 ∂P) = rA + rB) :
    Integrable (fun ω => A ω * B ω) P ∧
      (∫ ω, A ω * B ω ∂P) = 0 := by
  have hSumI : Integrable (fun ω => (A ω + B ω) ^ 2) P := by
    apply hU.congr
    filter_upwards [hAdd] with ω hω
    simp only [hω]
  have hProdI : Integrable (fun ω => A ω * B ω) P := by
    have hId : (fun ω => A ω * B ω) =
        (fun ω => ((A ω + B ω) ^ 2 - (A ω) ^ 2 - (B ω) ^ 2) / 2) := by
      funext ω
      ring
    rw [hId]
    exact ((hSumI.sub hA).sub hB).div_const 2
  have hExpand : (∫ ω, (A ω + B ω) ^ 2 ∂P) =
      (∫ ω, (A ω) ^ 2 ∂P) + (∫ ω, (B ω) ^ 2 ∂P) +
        2 * (∫ ω, A ω * B ω ∂P) := by
    calc
      (∫ ω, (A ω + B ω) ^ 2 ∂P) =
          ∫ ω, ((A ω) ^ 2 + (B ω) ^ 2) +
            2 * (A ω * B ω) ∂P := by
            congr 1
            funext ω
            ring
      _ = (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) +
            2 * (∫ ω, A ω * B ω ∂P) := by
          simpa only [Pi.add_apply, integral_const_mul] using
            (integral_add (hA.add hB) (hProdI.const_mul 2))
      _ = _ := by
          have hABsum : (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) =
              (∫ ω, (A ω) ^ 2 ∂P) + (∫ ω, (B ω) ^ 2 ∂P) := by
            simpa only [Pi.add_apply] using (integral_add hA hB)
          rw [hABsum]
  have hIntegrals : (∫ ω, (U ω) ^ 2 ∂P) =
      (∫ ω, (A ω + B ω) ^ 2 ∂P) := by
    apply integral_congr_ae
    filter_upwards [hAdd] with ω hω
    rw [hω]
  refine ⟨hProdI, ?_⟩
  rw [hIntegrals, hExpand, hMeanA, hMeanB] at hMeanU
  linarith
