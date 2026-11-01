-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_compensated_exponential_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:34:15.793029+00:00
-- url     : https://prove2.me/submissions/be975c84-831f-41a3-833c-56b086a58f4f

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i) :
    Martingale
      (fun t ω => ∑ i ∈ s, coeff i *
        Real.exp (rate i * X.X t ω - (t : ℝ) * X.ψ (rate i)))
      𝓕 P := by
  classical
  have hfinite :
      ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ rate i) →
        Martingale
          (fun t ω => ∑ i ∈ s, coeff i *
            Real.exp (rate i * X.X t ω -
              (t : ℝ) * X.ψ (rate i))) 𝓕 P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        change Martingale (0 : ℝ≥0 → Ω → ℝ) 𝓕 P
        exact MeasureTheory.martingale_zero ℝ 𝓕 P
    | @insert i s hnot ih =>
        intro hs
        have hi : 0 ≤ rate i :=
          hs i (Finset.mem_insert_self i s)
        have hrest : ∀ j ∈ s, 0 ≤ rate j := by
          intro j hj
          exact hs j (Finset.mem_insert_of_mem hj)
        have hsingle :
            Martingale
              (fun t ω => coeff i *
                Real.exp (rate i * X.X t ω -
                  (t : ℝ) * X.ψ (rate i))) 𝓕 P := by
          have hbase :=
            levy_compensated_exponential_martingale X (rate i) hi
          convert (hbase.smul (coeff i)) using 1
          ext t ω <;> simp only [Pi.smul_apply, smul_eq_mul]
        have htail := ih hrest
        convert hsingle.add htail using 1
        ext t ω <;> simp only [Finset.sum_insert hnot, Pi.add_apply]
  exact hfinite s hrate
