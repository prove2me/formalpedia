-- Prove2me | solution 1 for AvramDividend.Classical.chat06_ae_stopping_event_future_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:03:54.023982+00:00
-- url     : https://prove2.me/submissions/d1a02466-b355-472a-8d98-e7b2055e4b28

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- A stopping-index event may agree with an observable finite
past-cylinder only almost surely. This suffices to factor its
intersection probability against the independent complete future.
In particular, this remains valid when a full-path validity guard
modifies the count on a null set of infinite wait sequences. -/
theorem stopping_event_ae_past_future_factorisation
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace E]
    {P : Measure Ω}
    (N : Ω → ℕ) (n : ℕ)
    (past : Ω → A) (future : Ω → E)
    (hI : IndepFun past future P)
    (μ : Measure E) (hFuture : HasLaw future μ P)
    (hStop : ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω : Ω => past ω ∈ S))
    (B : Set E) (hB : MeasurableSet B) :
    P ({ω | N ω = n} ∩ {ω | future ω ∈ B}) =
      P {ω | N ω = n} * μ B := by
  obtain ⟨S, hS, hEq⟩ := hStop
  have hInter : (fun ω : Ω =>
      ω ∈ ({z | N z = n} ∩ {z | future z ∈ B})) =ᵐ[P]
      (fun ω : Ω =>
        ω ∈ ((past ⁻¹' S) ∩ (future ⁻¹' B))) := by
    filter_upwards [hEq] with ω hω
    change ((N ω = n) ∧ future ω ∈ B) =
      (past ω ∈ S ∧ future ω ∈ B)
    rw [hω]
  have hm : P {ω | N ω = n} = P (past ⁻¹' S) :=
    measure_congr hEq
  have hf : P (future ⁻¹' B) = μ B := by
    exact hFuture.measure_eq hB
  calc
    P ({ω | N ω = n} ∩ {ω | future ω ∈ B}) =
        P (past ⁻¹' S ∩ future ⁻¹' B) :=
      measure_congr hInter
    _ = P (past ⁻¹' S) * P (future ⁻¹' B) :=
      hI.measure_inter_preimage_eq_mul S B hS hB
    _ = P {ω | N ω = n} * μ B := by rw [← hm, hf]

end AvramChat06

open AvramChat06

theorem solution
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace E]
    {P : Measure Ω}
    (N : Ω → ℕ) (n : ℕ)
    (past : Ω → A) (future : Ω → E)
    (hI : IndepFun past future P)
    (μ : Measure E) (hFuture : HasLaw future μ P)
    (hStop : ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω : Ω => past ω ∈ S))
    (B : Set E) (hB : MeasurableSet B) :
    P ({ω | N ω = n} ∩ {ω | future ω ∈ B}) =
      P {ω | N ω = n} * μ B := by
  exact stopping_event_ae_past_future_factorisation
    N n past future hI μ hFuture hStop B hB
