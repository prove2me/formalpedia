-- Prove2me | solution 1 for BeliefDominance.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:34:17.173297+00:00
-- url     : https://prove2.me/submissions/a635b592-74ef-4a68-b3bc-626da3696730

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace Aux_BeliefDominance_theorem_5
open BeliefDominance

theorem mass_summable {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) : Summable (fun z => mass f y z) := by
  have h : Summable fun ω : Y × Z => (f ω).toReal :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  exact h.comp_injective (fun a b hab => by simpa using hab)

theorem mass_nonneg {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) (z : Z) : 0 ≤ mass f y z :=
  ENNReal.toReal_nonneg

theorem fY_nonneg {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) : 0 ≤ fY f y :=
  tsum_nonneg (mass_nonneg f y)

theorem mass_zero {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) (h : fY f y = 0) (z : Z) :
    mass f y z = 0 := by
  have := (mass_summable f y).le_tsum z (fun j _ => mass_nonneg f y j)
  unfold fY at h
  linarith [mass_nonneg f y z]

theorem key {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) (hP : P.WellPosed)
    (x x' : A₁ × (Y → A₂)) (hx : x ∈ P.space.strategies) (hx' : x' ∈ P.space.strategies)
    (y : Y) (h1 : x.1 = x'.1) (h2 : ∀ y' : Y, y' ≠ y → x.2 y' = x'.2 y')
    (f : PMF (Y × Z)) (hf : f ∈ P.Φ) :
    P.V x' f - P.V x f = fY f y * (P.V₂ x.1 (x'.2 y) y f - P.V₂ x.1 (x.2 y) y f) := by
  have hs := hP f hf x hx
  have hs' := hP f hf x' hx'
  have inj : Function.Injective (fun z : Z => (y, z)) := fun a b hab => by simpa using hab
  have hz : Summable fun z => P.U x.1 (x.2 y) z * mass f y z := hs.comp_injective inj
  have hz' : Summable fun z => P.U x.1 (x'.2 y) z * mass f y z := by
    refine (hs'.comp_injective inj).congr (fun z => ?_)
    simp [h1]
  have hdiff : P.V x' f - P.V x f =
      ∑' z, (P.U x.1 (x'.2 y) z * mass f y z - P.U x.1 (x.2 y) z * mass f y z) := by
    unfold Problem.V
    rw [← hs'.tsum_sub hs]
    symm
    have := inj.tsum_eq (f := fun ω : Y × Z => P.U x'.1 (x'.2 ω.1) ω.2 * mass f ω.1 ω.2 -
        P.U x.1 (x.2 ω.1) ω.2 * mass f ω.1 ω.2) ?_
    · simpa [h1] using this
    · intro ω hω
      refine ⟨ω.2, ?_⟩
      by_contra hne
      apply hω
      have : ω.1 ≠ y := by
        intro he; apply hne; rw [← he]
      simp only
      rw [h1, h2 ω.1 this, sub_self]
  rw [hdiff, hz'.tsum_sub hz]
  by_cases h0 : fY f y = 0
  · rw [h0, zero_mul]
    simp [mass_zero f y h0]
  · unfold Problem.V₂ fZ
    simp_rw [← mul_div_assoc]
    rw [tsum_div_const, tsum_div_const]
    field_simp

end Aux_BeliefDominance_theorem_5

open BeliefDominance Aux_BeliefDominance_theorem_5 in
theorem solution {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) (hP : P.WellPosed) :
    WeaklyConsistent P.space P.le P.le₂ := by
  intro x hx x' hx' y h1 h2
  have K := key P hP x x' hx hx' y h1 h2
  -- forward: le₂ a a' → le x x'
  have fwd : ∀ (u u' : A₁ × (Y → A₂)),
      (∀ f ∈ P.Φ, P.V u' f - P.V u f = fY f y * (P.V₂ x.1 (u'.2 y) y f - P.V₂ x.1 (u.2 y) y f)) →
      P.le₂ x.1 y (u.2 y) (u'.2 y) → P.le u u' := by
    intro u u' Ku h
    rcases h with ⟨hge, f0, hf0, hgt⟩ | hind
    · left
      refine ⟨fun f hf => ?_, f0, hf0.1, ?_⟩
      · have := Ku f hf
        by_cases h0 : fY f y = 0
        · rw [h0, zero_mul] at this; linarith
        · have hg := hge f ⟨hf, h0⟩
          have := fY_nonneg f y
          nlinarith
      · have := Ku f0 hf0.1
        have hpos : 0 < fY f0 y := lt_of_le_of_ne (fY_nonneg f0 y) (Ne.symm hf0.2)
        have : 0 < fY f0 y * (P.V₂ x.1 (u'.2 y) y f0 - P.V₂ x.1 (u.2 y) y f0) :=
          mul_pos hpos (by linarith)
        linarith
    · right
      intro f hf
      have := Ku f hf
      by_cases h0 : fY f y = 0
      · rw [h0, zero_mul] at this; linarith
      · rw [hind f ⟨hf, h0⟩, sub_self, mul_zero] at this; linarith
  -- backward: le x' x → le₂ a' a
  have bwd : P.le x' x → P.le₂ x.1 y (x'.2 y) (x.2 y) := by
    intro h
    rcases h with ⟨hge, f0, hf0, hgt⟩ | hind
    · left
      refine ⟨fun f hf => ?_, f0, ⟨hf0, ?_⟩, ?_⟩
      · have := K f hf.1
        have hpos : 0 < fY f y := lt_of_le_of_ne (fY_nonneg f y) (Ne.symm hf.2)
        have hg := hge f hf.1
        by_contra hc; push_neg at hc
        have : 0 < fY f y * (P.V₂ x.1 (x'.2 y) y f - P.V₂ x.1 (x.2 y) y f) :=
          mul_pos hpos (by linarith)
        linarith
      · intro h0
        have := K f0 hf0
        rw [h0, zero_mul] at this; linarith
      · have := K f0 hf0
        have hne : fY f0 y ≠ 0 := by
          intro h0; rw [h0, zero_mul] at this; linarith
        have hpos : 0 < fY f0 y := lt_of_le_of_ne (fY_nonneg f0 y) (Ne.symm hne)
        by_contra hc; push_neg at hc
        have : 0 ≤ fY f0 y * (P.V₂ x.1 (x'.2 y) y f0 - P.V₂ x.1 (x.2 y) y f0) :=
          mul_nonneg hpos.le (by linarith)
        linarith
    · right
      intro f hf
      have := K f hf.1
      have hpos : 0 < fY f y := lt_of_le_of_ne (fY_nonneg f y) (Ne.symm hf.2)
      rw [hind f hf.1, sub_self] at this
      have := (mul_eq_zero.mp this.symm).resolve_left hpos.ne'
      linarith
  have hle := fwd x x' K
  refine ⟨fun h => ⟨hle h.1, fun h' => h.2 (bwd h')⟩, hle⟩
