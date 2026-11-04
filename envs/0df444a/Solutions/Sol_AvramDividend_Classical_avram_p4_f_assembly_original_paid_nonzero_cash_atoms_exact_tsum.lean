-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:41:17.652839+00:00
-- url     : https://prove2.me/submissions/28860680-1c6a-4313-8ddc-8abcfd0e4f89

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original atomic Cash sum is exactly supported on paid nonzero source atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (A : Set ℝ)
    (μatom : Measure ℝ) (q : ℝ) :
    (∑' a : A,
      ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
        μatom {a.1}).toReal) =
    ∑' a : {a : A // a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
      μatom {a.1} ≠ 0},
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal := by
  let f : A → ℝ := fun a =>
    ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
      ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
      μatom {a.1}).toReal
  let B : Set A := {a | a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
    μatom {a.1} ≠ 0}
  have hsupport : Function.support f ⊆ B := by
    intro a ha
    change a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
      μatom {a.1} ≠ 0
    by_cases hPay : a.1 ∈ paymentTimes (ruinTime X x D ω)
    · by_cases hzero : μatom {a.1} = 0
      · exact False.elim (ha (by simp [f, hzero]))
      · exact ⟨hPay, hzero⟩
    · exact False.elim (ha (by simp [f, hPay]))
  change (∑' a : A, f a) =
    ∑' a : B,
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal
  calc
    (∑' a : A, f a) = ∑' a : B, f a.1 :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' a : B,
        (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
          μatom {a.1.1}).toReal := by
      apply tsum_congr
      intro a
      have hPay : a.1.1 ∈ paymentTimes (ruinTime X x D ω) := a.2.1
      simp [f, hPay]
