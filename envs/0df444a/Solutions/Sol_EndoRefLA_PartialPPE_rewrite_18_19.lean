-- Prove2me | solution 1 for EndoRefLA.PartialPPE.rewrite_18_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:17:36.972239+00:00
-- url     : https://prove2.me/submissions/8ec1d148-0210-4245-bc5a-2c71da2435e3

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_V_self_eq_Ex

namespace EndoRefLA.PartialPPE.R1819Aux

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



lemma gl_coe (Λ x : ℝ) : gl Λ (x : EReal) = ((x - (Λ - 1) * max (-x) 0 : ℝ) : EReal) := by
  unfold gl
  split_ifs with h
  · have hx : 0 ≤ x := by exact_mod_cast h
    rw [max_eq_right (by linarith)]; simp
  · have hx : x < 0 := by push_neg at h; exact_mod_cast h
    rw [max_eq_left (by linarith), ← EReal.coe_mul]
    congr 1; ring

lemma Ex_gl (P : Measure Ω) (Λ : ℝ) {W : Ω → EReal} (hW : Ex P W ≠ ⊥) :
    Ex P (fun ω => gl Λ (W ω)) = (((Ex P W).toReal -
      (Λ - 1) * ∫ ω, max (-(W ω).toReal) 0 ∂P : ℝ) : EReal) := by
  obtain ⟨hW1, hW2, hW3⟩ := Ex_spec P hW
  have hae : (fun ω => (gl Λ (W ω)).toReal) =ᵐ[P]
      fun ω => (W ω).toReal - (Λ - 1) * max (-(W ω).toReal) 0 := by
    filter_upwards [hW1] with ω h1
    lift W ω to ℝ using ⟨h1.2, h1.1⟩ with y
    rw [gl_coe, EReal.toReal_coe, EReal.toReal_coe]
  have hfin : ∀ᵐ ω ∂P, gl Λ (W ω) ≠ ⊥ ∧ gl Λ (W ω) ≠ ⊤ := by
    filter_upwards [hW1] with ω h1
    lift W ω to ℝ using ⟨h1.2, h1.1⟩ with y
    rw [gl_coe]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have hneg : Integrable (fun ω => max (-(W ω).toReal) 0) P := hW2.neg_part
  have hint : Integrable (fun ω => (gl Λ (W ω)).toReal) P :=
    (hW2.sub (hneg.const_mul (Λ - 1))).congr hae.symm
  rw [hW3, EReal.toReal_coe]
  unfold Ex
  rw [if_pos ⟨hfin, hint⟩, integral_congr_ae hae, integral_sub hW2 (hneg.const_mul (Λ - 1)),
    integral_const_mul]

lemma LamEta_eq {α lam η : ℝ} (hα : 0 < α) (hη : 0 ≤ η) :
    LamEta α lam η = 1 + (1 + α) * (lam - 1) * η / (1 + (1 + α) * η) := by
  have h1 : 0 < 1 + (1 + α) * η := by positivity
  unfold LamEta
  field_simp
  ring

end EndoRefLA.PartialPPE.R1819Aux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.R1819Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    (∀ η : ℝ, 0 < η → ∀ X : Ω → ℝ,
      V P α u u0 lam X X + (η : EReal) * V P α u u0 lam X B0 =
        (((1 + (1 + α) * η) / (1 + α) : ℝ) : EReal) * V P α u u0 (LamEta α lam η) X B0 +
          ((α / (1 + α) : ℝ) : EReal) * Ex P (fun ω => uE u u0 (B0 ω))) ∧
    (1 < lam →
      (∀ η : ℝ, 0 < η → LamEta α lam η ∈ Set.Ioo 1 lam) ∧
      StrictMonoOn (LamEta α lam) (Set.Ioi 0) ∧
      ∀ Λ ∈ Set.Ioo 1 lam, ∃ η : ℝ, 0 < η ∧ LamEta α lam η = Λ) := by
  have VXX : ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) :=
    V_self_eq_Ex P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
  have hBfin : Ex P (fun ω => uE u u0 (B0 ω)) ≠ ⊥ := hB0.2.2
  obtain ⟨b, hb⟩ : ∃ b : ℝ, Ex P (fun ω => uE u u0 (B0 ω)) = (b : EReal) :=
    ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hBfin).symm⟩
  refine ⟨fun η hη X => ?_, fun hl => ?_⟩
  · have hc : 0 < (1 + (1 + α) * η) / (1 + α) := by positivity
    rw [VXX]
    by_cases hX : Ex P (fun ω => uE u u0 (X ω)) = ⊥
    · rw [hX, EReal.bot_add, V_bot_of_Ex_bot P hα u u0 _ X B0 hX,
        EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
    obtain ⟨a, ha⟩ : ∃ a : ℝ, Ex P (fun ω => uE u u0 (X ω)) = (a : EReal) :=
      ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hX).symm⟩
    have hZ : Ex P (fun ω => uE u u0 (X ω) - uE u u0 (B0 ω)) ≠ ⊥ := by
      rw [Ex_sub P hX hBfin]; exact EReal.coe_ne_bot _
    have hZv := Ex_sub P hX hBfin
    set M := ∫ ω, max (-(uE u u0 (X ω) - uE u u0 (B0 ω)).toReal) 0 ∂P with hM
    have hG1 := Ex_gl P lam hZ
    have hG2 := Ex_gl P (LamEta α lam η) hZ
    rw [← hM] at hG1 hG2
    rw [hZv, EReal.toReal_coe, ha, hb, EReal.toReal_coe, EReal.toReal_coe] at hG1 hG2
    unfold V
    rw [hG1, hG2, ha, hb]
    have hΛ := LamEta_eq (lam := lam) hα hη.le
    rw [hΛ]
    have h1 : 0 < 1 + (1 + α) * η := by positivity
    have h2 : (0:ℝ) < 1 + α := by linarith
    norm_cast
    field_simp
    ring
  · have hA : ∀ η : ℝ, 0 ≤ η → LamEta α lam η = 1 + (1 + α) * (lam - 1) * η / (1 + (1 + α) * η) :=
      fun η hη => LamEta_eq hα hη
    have hl1 : 0 < lam - 1 := by linarith
    refine ⟨fun η hη => ?_, fun η1 h1 η2 h2 h12 => ?_, fun Λ hΛ => ?_⟩
    · rw [hA η hη.le]
      have hd : 0 < 1 + (1 + α) * η := by positivity
      constructor
      · have : 0 < (1 + α) * (lam - 1) * η / (1 + (1 + α) * η) := by positivity
        linarith
      · have : (1 + α) * (lam - 1) * η / (1 + (1 + α) * η) < lam - 1 := by
          rw [div_lt_iff₀ hd]; nlinarith
        linarith
    · have h1' : (0:ℝ) < η1 := h1
      have h2' : (0:ℝ) < η2 := h2
      rw [hA η1 h1'.le, hA η2 h2'.le]
      have hd1 : 0 < 1 + (1 + α) * η1 := by positivity
      have hd2 : 0 < 1 + (1 + α) * η2 := by positivity
      have : (1 + α) * (lam - 1) * η1 / (1 + (1 + α) * η1) <
          (1 + α) * (lam - 1) * η2 / (1 + (1 + α) * η2) := by
        rw [div_lt_div_iff₀ hd1 hd2]
        have hk : 0 < (1 + α) * (lam - 1) := by positivity
        nlinarith [mul_lt_mul_of_pos_left h12 hk]
      linarith
    · obtain ⟨hΛ1, hΛ2⟩ := hΛ
      have hden : 0 < (1 + α) * (lam - Λ) := by
        have : 0 < lam - Λ := by linarith
        positivity
      refine ⟨(Λ - 1) / ((1 + α) * (lam - Λ)), by
        have : 0 < Λ - 1 := by linarith
        positivity, ?_⟩
      have hη0 : 0 ≤ (Λ - 1) / ((1 + α) * (lam - Λ)) := by
        have : 0 < Λ - 1 := by linarith
        positivity
      rw [hA _ hη0]
      have hd : 1 + (1 + α) * ((Λ - 1) / ((1 + α) * (lam - Λ))) = (lam - 1) / (lam - Λ) := by
        field_simp; ring
      rw [hd]
      have hlΛ : lam - Λ ≠ 0 := by linarith
      field_simp
      ring
