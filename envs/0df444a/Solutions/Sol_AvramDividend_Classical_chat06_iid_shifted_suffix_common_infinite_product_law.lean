-- Prove2me | solution 1 for AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:21:57.806077+00:00
-- url     : https://prove2.me/submissions/3d340f64-d19d-4481-a846-939cd2764b5c

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory

/-- Every shifted suffix of an indexed independent family with the same
marginal law has that law's infinite-product distribution. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (ν : Measure ℝ) (hν : ∀ i, HasLaw (τ i) ν P)
    (n : ℕ) :
    HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω)
      (infinitePi (fun _ : ℕ => ν)) P := by
  have hinj : Function.Injective (fun j : ℕ => n + 1 + j) := by
    intro i j hij
    exact Nat.add_left_cancel hij
  have hSuffix : iIndepFun (fun j : ℕ => τ (n + 1 + j)) P :=
    hiid.precomp hinj
  have hm : AEMeasurable (fun ω (j : ℕ) => τ (n + 1 + j) ω) P :=
    (measurable_pi_iff.mpr (fun j => hτ (n + 1 + j))).aemeasurable
  exact hSuffix.hasLaw_infinitePi (fun j => hν (n + 1 + j)) hm
