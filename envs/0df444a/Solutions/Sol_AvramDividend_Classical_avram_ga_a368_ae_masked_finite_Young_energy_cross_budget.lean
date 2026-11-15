-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:26:25.577883+00:00
-- url     : https://prove2.me/submissions/574395d7-fb9f-46cf-8b76-cdebe5db91cf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i, A i ω →
      |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      ∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η) +
          M/2*|(r i ω)^2-(z i ω)^2| else 0 := by
  classical
  filter_upwards [hTaylor,hLip,hHess] with ω ht hl hh
  let f : ℕ → Unit → ℝ := fun i _ => s i ω
  let fu : ℕ → Unit → ℝ := fun i _ => u i ω
  let fv : ℕ → Unit → ℝ := fun i _ => v i ω
  let fd : ℕ → Unit → ℝ := fun i _ => d i ω
  let fh : ℕ → Unit → ℝ := fun i _ => h i ω
  let fr : ℕ → Unit → ℝ := fun i _ => r i ω
  let fz : ℕ → Unit → ℝ := fun i _ => z i ω
  let fA : ℕ → Unit → Prop := fun i _ => A i ω
  have h0 : ∀ i x, fA i x → 0 ≤ f i x :=
    fun i _ hi => hTime i ω hi
  have h1 : ∀ i x, fA i x →
      max (Real.exp (-(q*f i x)) *
      (fv i x-fu i x-fd i x*fr i x-fh i x/2*(fr i x)^2)) 0 ≤
        ε*(fr i x)^2 :=
    fun i _ hi => ht i hi
  have h2 : ∀ i x, fA i x →
      |fv i x-fu i x| ≤ L*|fr i x| :=
    fun i _ hi => hl i hi
  have h3 : ∀ i x, fA i x → |fh i x| ≤ M :=
    fun i _ hi => hh i hi
  have hz := avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
    S fA f fu fv fd fh fr fz q Δ ε L M η hq hΔ hε hL hM hη
    h0 h1 h2 h3 Unit.unit
  simpa only [fA,f,fu,fv,fd,fh,fr,fz] using hz
