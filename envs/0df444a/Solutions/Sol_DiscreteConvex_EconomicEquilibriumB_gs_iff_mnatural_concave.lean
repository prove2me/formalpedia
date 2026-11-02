-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibriumB.gs_iff_mnatural_concave
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:39:46.456184+00:00
-- url     : https://prove2.me/submissions/8c9e6ed4-50ce-4afe-ad68-e20e1471f271

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegGS

open Classical
open scoped Pointwise
open DiscreteConvex.EconomicEquilibriumB

private abbrev K0 := ULift.{0} Bool
private def t0 : K0 := ⟨true⟩
private def f0 : K0 := ⟨false⟩

private lemma t0_ne_f0 : t0 ≠ f0 := by decide
private lemma f0_ne_t0 : f0 ≠ t0 := by decide

private lemma univ_K0 : (Finset.univ : Finset K0) = {t0, f0} := by
  ext ⟨b⟩
  cases b <;> simp [t0, f0]

private lemma sum_K0 {M : Type*} [AddCommMonoid M] (g : K0 → M) :
    (∑ k : K0, g k) = g t0 + g f0 := by
  rw [univ_K0, Finset.sum_pair t0_ne_f0]

private def vecA : K0 → ℤ := fun k => if k = t0 then 2 else 0
private def vecB : K0 → ℤ := fun k => if k = t0 then 0 else 2

private def U0 (x : K0 → ℤ) : WithBot ℝ :=
  if x = vecA ∨ x = vecB then 0 else ⊥

private lemma mem_UDom_U0 (x : K0 → ℤ) : x ∈ UDom U0 ↔ x = vecA ∨ x = vecB := by
  simp [UDom, U0]
  tauto

private lemma toERealOfBot_zero : ToERealOfBot 0 = 0 := rfl
private lemma toERealOfBot_bot : ToERealOfBot ⊥ = ⊥ := rfl

private lemma U0_concave_extensible : IsConcaveExtensible U0 := by
  intro x hx
  have hx' : x = vecA ∨ x = vecB := (mem_UDom_U0 x).mp hx
  have hUx : U0 x = 0 := if_pos hx'
  rw [hUx, toERealOfBot_zero]
  unfold ConcaveClosureR
  apply le_antisymm
  · apply sInf_le
    refine ⟨fun _ => 0, 0, ?_, by simp⟩
    intro y
    by_cases hy : y = vecA ∨ y = vecB
    · have hUy : U0 y = 0 := if_pos hy
      rw [hUy, toERealOfBot_zero]
      simp
    · have hUy : U0 y = ⊥ := if_neg hy
      rw [hUy, toERealOfBot_bot]
      exact bot_le
  · apply le_sInf
    rintro v ⟨p, alpha, h1, rfl⟩
    have h1x := h1 x
    rw [hUx, toERealOfBot_zero] at h1x
    exact h1x

private lemma U0_bdd : ∃ N : ℤ, ∀ x ∈ UDom U0, ∀ k : K0, |x k| ≤ N := by
  refine ⟨2, fun x hx k => ?_⟩
  rcases (mem_UDom_U0 x).mp hx with rfl | rfl <;> rcases k with ⟨_ | _⟩ <;> simp [vecA, vecB, t0]

private lemma U0_dom_nonempty : (UDom U0).Nonempty :=
  ⟨vecA, (mem_UDom_U0 vecA).mpr (Or.inl rfl)⟩

private lemma not_MNaturalConcave_U0 : ¬ MNaturalConcave U0 := by
  intro hm
  have ha : vecA ∈ UDom U0 := (mem_UDom_U0 vecA).mpr (Or.inl rfl)
  have hb : vecB ∈ UDom U0 := (mem_UDom_U0 vecB).mpr (Or.inr rfl)
  have hi : t0 ∈ SuppPos vecA vecB := by
    unfold SuppPos
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [vecA, vecB]
  have h := hm.2 vecA ha vecB hb t0 hi
  have bot_add_wb : ∀ a : WithBot ℝ, (⊥ : WithBot ℝ) + a = ⊥ := by
    intro a; cases a <;> rfl
  have hA1 : U0 (fun w => vecA w - (if w = t0 then (1 : ℤ) else 0)) = ⊥ := by
    unfold U0
    rw [if_neg]
    rintro (h1 | h1)
    · have h2 := congr_fun h1 t0
      simp [vecA] at h2
    · have h2 := congr_fun h1 t0
      simp [vecA, vecB] at h2
  have hsup : (SuppNeg vecA vecB).sup (fun j =>
      U0 (fun w => vecA w - (if w = t0 then (1 : ℤ) else 0) + (if w = j then (1 : ℤ) else 0)) +
        U0 (fun w => vecB w + (if w = t0 then (1 : ℤ) else 0) - (if w = j then (1 : ℤ) else 0))) = ⊥ := by
    rw [Finset.sup_eq_bot_iff]
    intro j hj
    have hj_ne : t0 ≠ j := by
      intro h_eq
      subst h_eq
      unfold SuppNeg at hj
      rw [Finset.mem_filter] at hj
      have hj2 := hj.2
      simp [vecA, vecB] at hj2
    have hA2 : U0 (fun w => vecA w - (if w = t0 then (1 : ℤ) else 0) + (if w = j then (1 : ℤ) else 0)) = ⊥ := by
      unfold U0
      rw [if_neg]
      rintro (h1 | h1)
      · have h2 := congr_fun h1 t0
        simp [vecA, hj_ne] at h2
      · have h2 := congr_fun h1 t0
        simp [vecA, vecB, hj_ne] at h2
    rw [hA2, bot_add_wb]
  have hUa : U0 vecA = ((0 : ℝ) : WithBot ℝ) := if_pos (Or.inl rfl)
  have hUb : U0 vecB = ((0 : ℝ) : WithBot ℝ) := if_pos (Or.inr rfl)
  rw [hUa, hUb, hA1, bot_add_wb, hsup, max_self, ← WithBot.coe_add, add_zero] at h
  exact WithBot.coe_ne_bot (le_bot_iff.mp h)

private lemma priceShiftGen_vecA (p : K0 → ℝ) (p0 : ℝ) :
    PriceShiftGen U0 p p0 vecA = ((- (2 * p t0) + 2 * p0 : ℝ) : WithBot ℝ) := by
  unfold PriceShiftGen PriceShift
  have hUa : U0 vecA = ((0 : ℝ) : WithBot ℝ) := if_pos (Or.inl rfl)
  rw [hUa, sum_K0, sum_K0]
  simp only [vecA, if_neg f0_ne_t0, ↓reduceIte]
  rw [← WithBot.coe_add, ← WithBot.coe_add]
  congr 1
  push_cast
  ring

private lemma priceShiftGen_vecB (p : K0 → ℝ) (p0 : ℝ) :
    PriceShiftGen U0 p p0 vecB = ((- (2 * p f0) + 2 * p0 : ℝ) : WithBot ℝ) := by
  unfold PriceShiftGen PriceShift
  have hUb : U0 vecB = ((0 : ℝ) : WithBot ℝ) := if_pos (Or.inr rfl)
  rw [hUb, sum_K0, sum_K0]
  simp only [vecB, if_neg f0_ne_t0, ↓reduceIte]
  rw [← WithBot.coe_add, ← WithBot.coe_add]
  congr 1
  push_cast
  ring

private lemma priceShiftGen_other (p : K0 → ℝ) (p0 : ℝ) {z : K0 → ℤ} (hz : ¬ (z = vecA ∨ z = vecB)) :
    PriceShiftGen U0 p p0 z = ⊥ := by
  have hUz : U0 z = ⊥ := if_neg hz
  simp [PriceShiftGen, PriceShift, hUz]

private lemma vecA_mem_argMax {p : K0 → ℝ} {p0 : ℝ} (hle : p t0 ≤ p f0) :
    vecA ∈ ArgMaxBot (PriceShiftGen U0 p p0) := by
  intro y
  by_cases hy : y = vecA ∨ y = vecB
  · rcases hy with rfl | rfl
    · exact le_rfl
    · rw [priceShiftGen_vecA, priceShiftGen_vecB, WithBot.coe_le_coe]
      linarith
  · rw [priceShiftGen_other p p0 hy]
    exact bot_le

private lemma vecB_mem_argMax {p : K0 → ℝ} {p0 : ℝ} (hle : p f0 ≤ p t0) :
    vecB ∈ ArgMaxBot (PriceShiftGen U0 p p0) := by
  intro y
  by_cases hy : y = vecA ∨ y = vecB
  · rcases hy with rfl | rfl
    · rw [priceShiftGen_vecA, priceShiftGen_vecB, WithBot.coe_le_coe]
      linarith
    · exact le_rfl
  · rw [priceShiftGen_other p p0 hy]
    exact bot_le

private lemma mem_argMax_iff {p : K0 → ℝ} {p0 : ℝ} {x : K0 → ℤ}
    (hx : x ∈ ArgMaxBot (PriceShiftGen U0 p p0)) :
    (x = vecA ∧ p t0 ≤ p f0) ∨ (x = vecB ∧ p f0 ≤ p t0) := by
  by_cases h : x = vecA ∨ x = vecB
  · rcases h with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hxb := hx vecB
      rw [priceShiftGen_vecA, priceShiftGen_vecB, WithBot.coe_le_coe] at hxb
      linarith
    · right
      refine ⟨rfl, ?_⟩
      have hxa := hx vecA
      rw [priceShiftGen_vecA, priceShiftGen_vecB, WithBot.coe_le_coe] at hxa
      linarith
  · exfalso
    have hxa := hx vecA
    rw [priceShiftGen_other p p0 h, priceShiftGen_vecA] at hxa
    exact WithBot.coe_ne_bot (le_bot_iff.mp hxa)

private lemma NegGS_U0 : NegGS U0 := by
  intro p q p0 q0 hpq _ x hx _
  rcases mem_argMax_iff hx with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · rcases le_or_gt (q t0) (q f0) with hq | hq
    · refine ⟨vecA, vecA_mem_argMax hq, fun i _ => le_rfl, fun _ => le_rfl⟩
    · refine ⟨vecB, vecB_mem_argMax (le_of_lt hq), ?_, ?_⟩
      · intro i hpi
        rcases i with ⟨_ | _⟩
        · simp [vecA, vecB, t0]
        · exfalso
          have h1 : p t0 = q t0 := hpi
          have h2 : p f0 ≤ q f0 := hpq f0
          linarith
      · intro _
        simp [sum_K0, vecA, vecB, t0, f0]
  · rcases le_or_gt (q f0) (q t0) with hq | hq
    · refine ⟨vecB, vecB_mem_argMax hq, fun i _ => le_rfl, fun _ => le_rfl⟩
    · refine ⟨vecA, vecA_mem_argMax (le_of_lt hq), ?_, ?_⟩
      · intro i hpi
        rcases i with ⟨_ | _⟩
        · exfalso
          have h1 : p f0 = q f0 := hpi
          have h2 : p t0 ≤ q t0 := hpq t0
          linarith
        · simp [vecA, vecB, t0]
      · intro _
        simp [sum_K0, vecA, vecB, t0, f0]

theorem solution : ¬ ∀ {K : Type} [Fintype K] [DecidableEq K]
    (U : (K → ℤ) → WithBot ℝ) (_hconc : IsConcaveExtensible U)
    (_hbdd : ∃ N : ℤ, ∀ x ∈ UDom U, ∀ k, |x k| ≤ N) (_hne : (UDom U).Nonempty),
    MNaturalConcave U ↔ NegGS U := by
  intro h
  have hiff := h U0 U0_concave_extensible U0_bdd U0_dom_nonempty
  exact not_MNaturalConcave_U0 (hiff.mpr NegGS_U0)
