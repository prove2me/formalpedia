-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:32:13.184196+00:00
-- url     : https://prove2.me/submissions/165196d0-d7ba-4433-bb15-49c009657629

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a366_nested_small_fullcell_mask_energy_cross_Young_count_budget
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
    (q Δ δ ε η L M : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hη : 0 < η)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω ∧ |r i ω| < δ then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      (∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2 else 0) +
      (∑ i ∈ S, if A i ω then
        M/2*|(r i ω)^2-(z i ω)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(4*η)) := by
  classical
  let C : ℕ → Ω → Prop := fun i ω => A i ω ∧ |r i ω| < δ
  have hT : ∀ᵐ ω ∂P, ∀ i, C i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2 :=
    hTaylor.mono (fun ω hh i hi => hh i hi.1 hi.2)
  have hL' : ∀ᵐ ω ∂P, ∀ i, C i ω →
      |v i ω-u i ω| ≤ L*|r i ω| :=
    hLip.mono (fun ω hh i hi => hh i hi.1 hi.2)
  have hH' : ∀ᵐ ω ∂P, ∀ i, C i ω → |h i ω| ≤ M :=
    hHess.mono (fun ω hh i hi => hh i hi.1 hi.2)
  have hB := avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
    (P := P) S C s u v d h r z q Δ ε L M η
    hq hΔ hε hL hM hη (fun i ω hi => hTime i ω hi.1) hT hL' hH'
  filter_upwards [hB] with ω hw
  let a : ℕ → ℝ := fun i => (ε+η)*(r i ω)^2
  let b : ℕ → ℝ := fun i => M/2*|(r i ω)^2-(z i ω)^2|
  let c : ℝ := (q*Δ*L)^2/(4*η)
  have ha : ∀ i, 0 ≤ a i :=
    fun i => mul_nonneg (add_nonneg hε hη.le) (sq_nonneg _)
  have hb : ∀ i, 0 ≤ b i :=
    fun i => mul_nonneg (div_nonneg hM (by norm_num)) (abs_nonneg _)
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (by positivity)
  have hy := avram_ga_a366_nested_small_fullcell_mask_energy_cross_Young_count_budget
    S (fun i => C i ω) (fun i => A i ω) a b c ha hb hc
    (fun i hi => hi.1)
  calc
    max (∑ i ∈ S, if C i ω then
      Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
        Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
      ∑ i ∈ S, if C i ω then a i+c+b i else 0 := hw
    _ = ∑ i ∈ S, if C i ω then a i+b i+c else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ ≤ (∑ i ∈ S, if A i ω then a i else 0) +
      (∑ i ∈ S, if A i ω then b i else 0) +
      (S.card : ℝ)*c := hy
