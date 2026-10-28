-- Prove2me | solution 1 for AvramDividend.Classical.directed_stieltjes_prefixes_determine_union_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:51:58.322998+00:00
-- url     : https://prove2.me/submissions/607a75c4-d1eb-4a45-bc53-2b3e3b2f6040

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Equality of weighted Stieltjes rewards along a countable directed
family of surviving prefixes determines the reward on their union. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι]
    (μ ν : Measure α) (f : α → ℝ≥0∞) (s : ι → Set α)
    (hd : Directed (fun (a b : Set α) => a ⊆ b) s)
    (hPrefix : ∀ i : ι,
      (∫⁻ x in s i, f x ∂μ) = (∫⁻ x in s i, f x ∂ν)) :
    (∫⁻ x in ⋃ i, s i, f x ∂μ) =
      (∫⁻ x in ⋃ i, s i, f x ∂ν) := by
  calc
    (∫⁻ x in ⋃ i, s i, f x ∂μ) =
        ⨆ i, (∫⁻ x in s i, f x ∂μ) :=
      setLIntegral_iUnion_of_directed f hd
    _ = ⨆ i, (∫⁻ x in s i, f x ∂ν) :=
      iSup_congr hPrefix
    _ = (∫⁻ x in ⋃ i, s i, f x ∂ν) :=
      (setLIntegral_iUnion_of_directed f hd).symm
