-- Prove2me | solution 1 for BeliefDominance.branch_identity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T19:29:59.099132+00:00
-- url     : https://prove2.me/submissions/33f35622-efc1-4f31-98b1-38c64fe82c57

import Definitions.Def_BeliefDominance_Problem

namespace Aux_BeliefDominance_branch_identity
open BeliefDominance

private theorem mass_summable {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) :
    Summable (fun z => mass f y z) := by
  have h : Summable fun ω : Y × Z => (f ω).toReal :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  exact h.comp_injective (fun a b hab => by simpa using hab)

private theorem mass_nonneg {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) (z : Z) :
    0 ≤ mass f y z :=
  ENNReal.toReal_nonneg

private theorem mass_zero {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) (h : fY f y = 0) (z : Z) :
    mass f y z = 0 := by
  have hle := (mass_summable f y).le_tsum z (fun j _ => mass_nonneg f y j)
  unfold fY at h
  linarith [mass_nonneg f y z]

end Aux_BeliefDominance_branch_identity

open BeliefDominance Aux_BeliefDominance_branch_identity

theorem solution {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) (hP : P.WellPosed)
    {x x' : A₁ × (Y → A₂)} (hx : x ∈ P.space.strategies) (hx' : x' ∈ P.space.strategies)
    (y : Y) (h₁ : x.1 = x'.1) (h₂ : ∀ y' : Y, y' ≠ y → x.2 y' = x'.2 y')
    {f : PMF (Y × Z)} (hf : f ∈ P.Φ) :
    (fY f y ≠ 0 →
      P.V x' f - P.V x f = fY f y * (P.V₂ x.1 (x'.2 y) y f - P.V₂ x.1 (x.2 y) y f)) ∧
    (fY f y = 0 → (∀ z : Z, mass f y z = 0) ∧ P.V x' f = P.V x f) := by
  have hs := hP f hf x hx
  have hs' := hP f hf x' hx'
  have inj : Function.Injective (fun z : Z => (y, z)) := fun a b hab => by simpa using hab
  have hz : Summable fun z => P.U x.1 (x.2 y) z * mass f y z := hs.comp_injective inj
  have hz' : Summable fun z => P.U x.1 (x'.2 y) z * mass f y z := by
    refine (hs'.comp_injective inj).congr (fun z => ?_)
    simp [h₁]
  have hdiff : P.V x' f - P.V x f =
      ∑' z, (P.U x.1 (x'.2 y) z * mass f y z - P.U x.1 (x.2 y) z * mass f y z) := by
    unfold Problem.V
    rw [← hs'.tsum_sub hs]
    symm
    have hts := inj.tsum_eq (f := fun ω : Y × Z =>
      P.U x'.1 (x'.2 ω.1) ω.2 * mass f ω.1 ω.2 - P.U x.1 (x.2 ω.1) ω.2 * mass f ω.1 ω.2) ?_
    · simpa [h₁] using hts
    · intro ω hω
      refine ⟨ω.2, ?_⟩
      by_contra hne
      apply hω
      have hyne : ω.1 ≠ y := by
        intro he
        exact hne (by rw [← he])
      simp only
      rw [h₁, h₂ ω.1 hyne, sub_self]
  refine ⟨fun hne => ?_, fun h0 => ?_⟩
  · rw [hdiff, hz'.tsum_sub hz]
    unfold Problem.V₂ fZ
    simp_rw [← mul_div_assoc]
    rw [tsum_div_const, tsum_div_const]
    field_simp [hne]
  · have hmz : ∀ z : Z, mass f y z = 0 := mass_zero f y h0
    refine ⟨hmz, ?_⟩
    have hzero : P.V x' f - P.V x f = 0 := by
      rw [hdiff]
      simp [hmz]
    linarith
