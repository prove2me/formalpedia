-- Prove2me | solution 1 for ConnesGreen.canonical_raw_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T03:01:45.863817+00:00
-- url     : https://prove2.me/submissions/29353a02-3c0e-48eb-ab02-d03684d81ab6

import Definitions.Def_ConnesGreen_canonical_model
import Theorems.Thm_ConnesGreen_actual_column_realization
import Theorems.Thm_WeilDefect_ConnesNative_actual_Green_column_energy_summable
import Theorems.Thm_ConnesRZNative_bounded_column_synthesis_with_adjoint_energy
set_option autoImplicit false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

private def normCoefficients {ι H : Type*} [NormedAddCommGroup H]
    (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) : ℓ²(ι, ℂ) :=
  ⟨fun i => (‖v i‖ : ℂ), memℓp_gen (by
    simpa [Complex.norm_real, Real.norm_eq_abs, Real.rpow_natCast] using hv)⟩

private theorem series_summable {ι H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    [NormedSpace ℂ H] (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : Summable (fun i => u i • v i) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hh := (lp.tsum_mul_le_mul_norm hp u (normCoefficients v hv)).1
  have hs : Summable (fun i => ‖u i • v i‖) := by
    simpa [norm_smul, normCoefficients, Complex.norm_real, Real.norm_eq_abs] using hh
  exact hs.of_norm

private theorem column_norm (t : ℝ) (hc : ColumnRealization t) (ρ : CriticalZeros) :
    ‖rawColumn t ρ‖ ^ 2 = weightedEnergy t ρ := by
  have hm := (hc ρ).2.2.2.2
  change ‖((Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) •
    sourceEmbed t (actualGreenSource ρ) : Physical t)‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _), hm]
  rfl
end ConnesGreen

theorem solution (t : ℝ) (ht : 0 < t) : ConnesGreen.RawSynthesis t := by
  have hc := ConnesGreen.actual_column_realization t ht
  have hs : Summable (ConnesGreen.weightedEnergy t) :=
    WeilDefect.ConnesNative.actual_Green_column_energy_summable t ht
  have hv : Summable (fun ρ => ‖ConnesGreen.rawColumn t ρ‖ ^ 2) := by
    simpa only [ConnesGreen.column_norm t hc] using hs
  obtain ⟨S, hseries, hbasis, hcoord, hnorm, hbound, hunique⟩ :=
    ConnesRZNative.bounded_column_synthesis_with_adjoint_energy (ConnesGreen.rawColumn t) hv
  refine ⟨hs, S, ConnesGreen.series_summable _ hv, hseries, ?_, hcoord, hnorm, ?_, ?_⟩
  · intro ρ
    convert hbasis ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · simpa only [ConnesGreen.column_norm t hc] using hbound
  · intro T hT
    apply hunique T
    intro ρ
    convert hT ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
