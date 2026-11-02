-- Prove2me | solution 1 for EndoRefLA.PartialPPE.problem_10_iff_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:15:53.413219+00:00
-- url     : https://prove2.me/submissions/05bfe324-a2d2-4485-bf2f-e050bd4e884c

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_V_self_eq_Ex

namespace EndoRefLA.PartialPPE.P10Aux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Ex_congr (P : Measure Ω) {Y Y' : Ω → EReal} (h : Y =ᵐ[P] Y') : Ex P Y = Ex P Y' := by
  have h1 : (∀ᵐ ω ∂P, Y ω ≠ ⊥ ∧ Y ω ≠ ⊤) ↔ (∀ᵐ ω ∂P, Y' ω ≠ ⊥ ∧ Y' ω ≠ ⊤) := by
    constructor
    · intro hh; filter_upwards [hh, h] with ω h1 h2; rwa [← h2]
    · intro hh; filter_upwards [hh, h] with ω h1 h2; rwa [h2]
  have h2' : (fun ω => (Y ω).toReal) =ᵐ[P] (fun ω => (Y' ω).toReal) := by
    filter_upwards [h] with ω hω; rw [hω]
  have h2 : Integrable (fun ω => (Y ω).toReal) P ↔ Integrable (fun ω => (Y' ω).toReal) P :=
    integrable_congr h2'
  unfold Ex
  rw [integral_congr_ae h2']
  split_ifs with ha hb hb
  · rfl
  · exact absurd ⟨h1.1 ha.1, h2.1 ha.2⟩ hb
  · exact absurd ⟨h1.2 hb.1, h2.2 hb.2⟩ ha
  · rfl

lemma Ex_ne_top (P : Measure Ω) (Y : Ω → EReal) : Ex P Y ≠ ⊤ := by
  unfold Ex; split_ifs <;> simp

lemma V_congr (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    {X X' B B' : Ω → ℝ} (hX : X =ᵐ[P] X') (hB : B =ᵐ[P] B') :
    V P α u u0 lam X B = V P α u u0 lam X' B' := by
  unfold V
  rw [Ex_congr P (Y := fun ω => uE u u0 (X ω)) (Y' := fun ω => uE u u0 (X' ω))
      (by filter_upwards [hX] with ω h; rw [h]),
    Ex_congr P (Y := fun ω => gl lam (uE u u0 (X ω) - uE u u0 (B ω)))
      (Y' := fun ω => gl lam (uE u u0 (X' ω) - uE u u0 (B' ω)))
      (by filter_upwards [hX, hB] with ω h h'; rw [h, h'])]

lemma mul_Ex_ne_top (P : Measure Ω) {α : ℝ} (hα : 0 < α) (Y : Ω → EReal) :
    (α : EReal) * Ex P Y ≠ ⊤ := by
  unfold Ex; split_ifs
  · rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  · rw [EReal.coe_mul_bot_of_pos hα]; exact bot_ne_top

lemma V_ne_top (P : Measure Ω) {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (X B : Ω → ℝ) : V P α u u0 lam X B ≠ ⊤ :=
  EReal.add_ne_top (Ex_ne_top _ _) (mul_Ex_ne_top P hα _)

lemma V_bot_of_Ex_bot (P : Measure Ω) {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (X B : Ω → ℝ) (h : Ex P (fun ω => uE u u0 (X ω)) = ⊥) : V P α u u0 lam X B = ⊥ := by
  unfold V; rw [h, EReal.bot_add]

lemma Ex_ne_bot_of_V (P : Measure Ω) {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (X B : Ω → ℝ) (h : V P α u u0 lam X B ≠ ⊥) : Ex P (fun ω => uE u u0 (X ω)) ≠ ⊥ :=
  fun h' => h (V_bot_of_Ex_bot P hα u u0 lam X B h')

lemma Ex_spec (P : Measure Ω) {Y : Ω → EReal} (h : Ex P Y ≠ ⊥) :
    (∀ᵐ ω ∂P, Y ω ≠ ⊥ ∧ Y ω ≠ ⊤) ∧ Integrable (fun ω => (Y ω).toReal) P ∧
      Ex P Y = ((∫ ω, (Y ω).toReal ∂P : ℝ) : EReal) := by
  unfold Ex at h ⊢
  split_ifs at h ⊢ with hc
  · exact ⟨hc.1, hc.2, rfl⟩
  · exact absurd rfl h

lemma Ex_sub (P : Measure Ω) {Y Z : Ω → EReal} (hY : Ex P Y ≠ ⊥) (hZ : Ex P Z ≠ ⊥) :
    Ex P (fun ω => Y ω - Z ω) = (((Ex P Y).toReal - (Ex P Z).toReal : ℝ) : EReal) := by
  obtain ⟨hY1, hY2, hY3⟩ := Ex_spec P hY
  obtain ⟨hZ1, hZ2, hZ3⟩ := Ex_spec P hZ
  have hae : (fun ω => (Y ω - Z ω).toReal) =ᵐ[P] fun ω => (Y ω).toReal - (Z ω).toReal := by
    filter_upwards [hY1, hZ1] with ω h1 h2
    lift Y ω to ℝ using ⟨h1.2, h1.1⟩ with y
    lift Z ω to ℝ using ⟨h2.2, h2.1⟩ with z
    rw [← EReal.coe_sub, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe]
  have hfin : ∀ᵐ ω ∂P, Y ω - Z ω ≠ ⊥ ∧ Y ω - Z ω ≠ ⊤ := by
    filter_upwards [hY1, hZ1] with ω h1 h2
    lift Y ω to ℝ using ⟨h1.2, h1.1⟩ with y
    lift Z ω to ℝ using ⟨h2.2, h2.1⟩ with z
    rw [← EReal.coe_sub]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have hint : Integrable (fun ω => (Y ω - Z ω).toReal) P :=
    (hY2.sub hZ2).congr hae.symm
  rw [hY3, hZ3, EReal.toReal_coe, EReal.toReal_coe]
  unfold Ex
  rw [if_pos ⟨hfin, hint⟩, integral_congr_ae hae, integral_sub hY2 hZ2]

lemma V_one_eq (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (X B : Ω → ℝ)
    (hX : Ex P (fun ω => uE u u0 (X ω)) ≠ ⊥) (hB : Ex P (fun ω => uE u u0 (B ω)) ≠ ⊥) :
    V P α u u0 1 X B = (((1 + α) * (Ex P (fun ω => uE u u0 (X ω))).toReal -
      α * (Ex P (fun ω => uE u u0 (B ω))).toReal : ℝ) : EReal) := by
  have hgl : ∀ z : EReal, gl 1 z = z := by
    intro z; unfold gl; split_ifs <;> simp
  unfold V
  simp only [hgl]
  rw [Ex_sub P hX hB]
  obtain ⟨-, -, h3⟩ := Ex_spec P hX
  rw [h3, EReal.toReal_coe, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1; ring



lemma Ex_mono_of_le (P : Measure Ω) {W Z : Ω → EReal} (hZ : Ex P Z ≠ ⊥)
    (h : ∀ᵐ ω ∂P, W ω ≤ Z ω) : Ex P W ≤ Ex P Z := by
  by_cases hW : Ex P W = ⊥
  · rw [hW]; exact bot_le
  obtain ⟨hW1, hW2, hW3⟩ := Ex_spec P hW
  obtain ⟨hZ1, hZ2, hZ3⟩ := Ex_spec P hZ
  rw [hW3, hZ3]
  apply EReal.coe_le_coe_iff.mpr
  apply integral_mono_ae hW2 hZ2
  filter_upwards [h, hW1, hZ1] with ω h1 h2 h3
  exact EReal.toReal_le_toReal h1 h2.1 h3.2

lemma gl_le {lam : ℝ} (hlam : 1 ≤ lam) (z : EReal) : gl lam z ≤ z := by
  unfold gl
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    induction z using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos (by linarith)]
    | coe x =>
      rw [← EReal.coe_mul]
      apply EReal.coe_le_coe_iff.mpr
      have : x < 0 := by exact_mod_cast h
      nlinarith
    | top => exact absurd h (not_lt.mpr le_top)

/-- `V_λ(Y|X) ≤ E[u(X)]` whenever `E[u(Y)] ≤ E[u(X)]`, `E[u(X)]` finite, and `λ ≥ 1`. -/
lemma V_le_self (P : Measure Ω) {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (u0 : EReal) {lam : ℝ}
    (hlam : 1 ≤ lam) (Y X : Ω → ℝ) (hX : Ex P (fun ω => uE u u0 (X ω)) ≠ ⊥)
    (hYX : Ex P (fun ω => uE u u0 (Y ω)) ≤ Ex P (fun ω => uE u u0 (X ω))) :
    V P α u u0 lam Y X ≤ Ex P (fun ω => uE u u0 (X ω)) := by
  by_cases hY : Ex P (fun ω => uE u u0 (Y ω)) = ⊥
  · rw [V_bot_of_Ex_bot P hα u u0 lam Y X hY]; exact bot_le
  have hsub := Ex_sub P hY hX
  have hle : Ex P (fun ω => gl lam (uE u u0 (Y ω) - uE u u0 (X ω))) ≤
      Ex P (fun ω => uE u u0 (Y ω) - uE u u0 (X ω)) := by
    apply Ex_mono_of_le P (by rw [hsub]; exact EReal.coe_ne_bot _)
    exact Filter.Eventually.of_forall (fun ω => gl_le hlam _)
  rw [hsub] at hle
  unfold V
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Ex P (fun ω => uE u u0 (Y ω)) = (a : EReal) :=
    ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hY).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, Ex P (fun ω => uE u u0 (X ω)) = (b : EReal) :=
    ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hX).symm⟩
  rw [ha, hb] at hYX hle ⊢
  rw [EReal.toReal_coe, EReal.toReal_coe] at hle
  have hab : a ≤ b := EReal.coe_le_coe_iff.mp hYX
  by_cases hg : Ex P (fun ω => gl lam (uE u u0 (Y ω) - uE u u0 (X ω))) = ⊥
  · rw [hg, EReal.coe_mul_bot_of_pos hα, EReal.add_bot]; exact bot_le
  obtain ⟨g, hg'⟩ : ∃ g : ℝ, Ex P (fun ω => gl lam (uE u u0 (Y ω) - uE u u0 (X ω))) = (g : EReal) :=
    ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hg).symm⟩
  rw [hg'] at hle ⊢
  have hgl : g ≤ a - b := EReal.coe_le_coe_iff.mp hle
  rw [← EReal.coe_mul, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  nlinarith

end EndoRefLA.PartialPPE.P10Aux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.P10Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (f : ℝ → ℝ) (c0 : ℝ)
    (hmax : ∃ Xs ∈ Ycal P ρ x0 α u u0 lam B0 f c0, ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam Xs Xs) :
    ∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔
      (X ∈ Ycal P ρ x0 α u u0 lam B0 f c0 ∧ ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam X X) := by
  have VXX : ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) :=
    V_self_eq_Ex P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
  have hfin : ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, Ex P (fun ω => uE u u0 (Y ω)) ≠ ⊥ := by
    rintro Y ⟨-, w, hw, -⟩
    exact Ex_ne_bot_of_V P hα u u0 lam Y B0 (by rw [hw]; exact EReal.coe_ne_bot _)
  have hPE : ∀ X ∈ Ycal P ρ x0 α u u0 lam B0 f c0,
      (∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam X X) →
      IsPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X := by
    intro X hX hXm
    refine ⟨hX, ⟨hX.1.1, hX.1.2.1, hfin X hX⟩, fun Y hY => ?_⟩
    have h := hXm Y hY
    rw [VXX, VXX] at h
    rw [VXX]
    exact V_le_self P hα u u0 hlam Y X (hfin X hX) h
  obtain ⟨Xs, hXs, hXsm⟩ := hmax
  intro X
  constructor
  · rintro ⟨hPEX, hPPE⟩
    exact ⟨hPEX.1, fun Y hY => (hXsm Y hY).trans (hPPE Xs (hPE Xs hXs hXsm))⟩
  · rintro ⟨hX, hXm⟩
    exact ⟨hPE X hX hXm, fun Z hZ => hXm Z hZ.1⟩
