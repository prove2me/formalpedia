-- Prove2me | solution 1 for EndoRefLA.PartialPPE.value_strictMono
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:23:18.382468+00:00
-- url     : https://prove2.me/submissions/b771ea1c-2a38-4998-85fa-1ae1d19c5cdb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_V_self_eq_Ex
import Theorems.Thm_EndoRefLA_PartialPPE_theorem_1
import Theorems.Thm_EndoRefLA_PartialPPE_proposition_1_furthermore
import Theorems.Thm_EndoRefLA_PartialPPE_rewrite_18_19

namespace EndoRefLA.PartialPPE.SMAux

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


lemma V_fin (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (Λ : ℝ) (X B : Ω → ℝ)
    (hX : Ex P (fun ω => uE u u0 (X ω)) ≠ ⊥) (hB : Ex P (fun ω => uE u u0 (B ω)) ≠ ⊥) :
    V P α u u0 Λ X B ≠ ⊥ := by
  have hZ : Ex P (fun ω => uE u u0 (X ω) - uE u u0 (B ω)) ≠ ⊥ := by
    rw [Ex_sub P hX hB]; exact EReal.coe_ne_bot _
  unfold V
  rw [Ex_gl P Λ hZ, ← EReal.coe_toReal (Ex_ne_top P _) hX, ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_ne_bot _

end EndoRefLA.PartialPPE.SMAux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.SMAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    StrictMonoOn (fun Λ : ℝ => (V P α u u0 lam (Xex Λ) B0).toReal) (Set.Ico 1 (lamCap P ρ x0 α lam u B0 νG νL)) := by
  set L := lamCap P ρ x0 α lam u B0 νG νL with hLdef
  have hBfin : Ex P (fun ω => uE u u0 (B0 ω)) ≠ ⊥ := hB0.2.2
  have huniq : ∀ Λ : ℝ, 1 ≤ Λ → ∀ X, IsOptEx P ρ x0 α u u0 B0 Λ X → X =ᵐ[P] Xex Λ := by
    intro Λ hΛ X hX
    obtain ⟨⟨ν, -, -, -, hu1, -⟩, -⟩ := theorem_1 P ρ x0 α Λ u u0 B0 hρ hx0 hα hΛ hu hB0
    exact (hu1 X hX).trans (hu1 _ (hXex Λ hΛ)).symm
  have hEu : ∀ Λ : ℝ, 1 ≤ Λ → Ex P (fun ω => uE u u0 (Xex Λ ω)) ≠ ⊥ := by
    intro Λ hΛ
    obtain ⟨⟨ν, -, -, -, hu1, hne⟩, -⟩ := theorem_1 P ρ x0 α Λ u u0 B0 hρ hx0 hα hΛ hu hB0
    apply Ex_ne_bot_of_V P hα u u0 Λ _ B0
    rwa [V_congr P α u u0 Λ (hu1 _ (hXex Λ hΛ)) (Filter.EventuallyEq.refl _ _)]
  have hLle : L ≤ lam := by
    rw [hLdef]; unfold lamCap; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have VXX : ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) :=
    V_self_eq_Ex P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
  obtain ⟨b, hb⟩ : ∃ b : ℝ, Ex P (fun ω => uE u u0 (B0 ω)) = (b : EReal) :=
    ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hBfin).symm⟩
  -- the identity (18)-(19) in real numbers, for prospects with finite expected utility
  have hid : ∀ η : ℝ, 0 < η → ∀ Y : Ω → ℝ, Ex P (fun ω => uE u u0 (Y ω)) ≠ ⊥ →
      (Ex P (fun ω => uE u u0 (Y ω))).toReal + η * (V P α u u0 lam Y B0).toReal =
        (1 + (1 + α) * η) / (1 + α) * (V P α u u0 (LamEta α lam η) Y B0).toReal +
          α / (1 + α) * b := by
    intro η hη Y hY
    have h := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).1 η hη Y
    obtain ⟨a, ha⟩ : ∃ a : ℝ, Ex P (fun ω => uE u u0 (Y ω)) = (a : EReal) :=
      ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hY).symm⟩
    obtain ⟨w, hw⟩ : ∃ w : ℝ, V P α u u0 lam Y B0 = (w : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 lam Y B0) (V_fin P α u u0 lam Y B0 hY hBfin)).symm⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, V P α u u0 (LamEta α lam η) Y B0 = (q : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 _ Y B0) (V_fin P α u u0 _ Y B0 hY hBfin)).symm⟩
    rw [VXX, hb, ha, hw, hq] at h
    rw [ha, hw, hq, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe]
    exact_mod_cast h
  have hVc : ∀ Λ' : ℝ, ∀ Y : Ω → ℝ, Ex P (fun ω => uE u u0 (Y ω)) ≠ ⊥ →
      V P α u u0 Λ' Y B0 = ((V P α u u0 Λ' Y B0).toReal : EReal) := fun Λ' Y hY =>
    (EReal.coe_toReal (V_ne_top P hα u u0 Λ' Y B0) (V_fin P α u u0 Λ' Y B0 hY hBfin)).symm
  intro Λ1 h1 Λ2 h2 h12
  simp only
  have hΛ1 : 1 ≤ Λ1 := h1.1
  have hΛ2 : 1 ≤ Λ2 := le_trans h1.1 h12.le
  have hlam1 : 1 < lam := lt_of_le_of_lt h1.1 (lt_trans h12 (lt_of_lt_of_le h2.2 hLle))
  obtain ⟨-, hEmono, hsurj⟩ := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).2 hlam1
  obtain ⟨η2, hη2, hη2Λ⟩ := hsurj Λ2 ⟨lt_of_le_of_lt h1.1 h12, lt_of_lt_of_le h2.2 hLle⟩
  set X1 := Xex Λ1 with hX1
  set X2 := Xex Λ2 with hX2
  set A1 := (Ex P (fun ω => uE u u0 (X1 ω))).toReal
  set A2 := (Ex P (fun ω => uE u u0 (X2 ω))).toReal
  set B1 := (V P α u u0 lam X1 B0).toReal
  set B2 := (V P α u u0 lam X2 B0).toReal
  have hc2 : 0 < (1 + (1 + α) * η2) / (1 + α) := by positivity
  -- optimality of X2 at Λ2
  have hI2 : A1 + η2 * B1 ≤ A2 + η2 * B2 := by
    rw [hid η2 hη2 X1 (hEu Λ1 hΛ1), hid η2 hη2 X2 (hEu Λ2 hΛ2), hη2Λ]
    have h := (hXex Λ2 hΛ2).2 X1 (hXex Λ1 hΛ1).1
    rw [hVc Λ2 X1 (hEu Λ1 hΛ1), hVc Λ2 X2 (hEu Λ2 hΛ2)] at h
    have h' := EReal.coe_le_coe_iff.mp h
    nlinarith [mul_le_mul_of_nonneg_left h' hc2.le]
  -- optimality of X1 at Λ1, with η1 = 0 when Λ1 = 1
  obtain ⟨η1, hη1, hη12, hI1⟩ : ∃ η1 : ℝ, 0 ≤ η1 ∧ η1 < η2 ∧ A2 + η1 * B2 ≤ A1 + η1 * B1 := by
    rcases eq_or_lt_of_le hΛ1 with he | hgt
    · refine ⟨0, le_rfl, hη2, ?_⟩
      have h := (hXex Λ1 hΛ1).2 X2 (hXex Λ2 hΛ2).1
      have hE1 := hEu Λ1 hΛ1
      subst he
      rw [V_one_eq P α u u0 X2 B0 (hEu Λ2 hΛ2) hBfin,
        V_one_eq P α u u0 (Xex 1) B0 hE1 hBfin] at h
      have h' := EReal.coe_le_coe_iff.mp h
      have : A2 ≤ A1 := by
        have h'' : (1 + α) * A2 ≤ (1 + α) * A1 := by linarith
        exact le_of_mul_le_mul_left h'' (by linarith)
      linarith
    · obtain ⟨η1, hη1, hη1Λ⟩ := hsurj Λ1 ⟨hgt, lt_trans h12 (lt_of_lt_of_le h2.2 hLle)⟩
      have hlt : η1 < η2 := by
        by_contra hcon
        push_neg at hcon
        rcases eq_or_lt_of_le hcon with he | hl
        · rw [he] at hη2Λ; rw [hη2Λ] at hη1Λ; linarith
        · have := hEmono (Set.mem_Ioi.mpr hη2) (Set.mem_Ioi.mpr hη1) hl
          rw [hη1Λ, hη2Λ] at this; linarith
      refine ⟨η1, hη1.le, hlt, ?_⟩
      have hc1 : 0 < (1 + (1 + α) * η1) / (1 + α) := by positivity
      rw [hid η1 hη1 X1 (hEu Λ1 hΛ1), hid η1 hη1 X2 (hEu Λ2 hΛ2), hη1Λ]
      have h := (hXex Λ1 hΛ1).2 X2 (hXex Λ2 hΛ2).1
      rw [hVc Λ1 X1 (hEu Λ1 hΛ1), hVc Λ1 X2 (hEu Λ2 hΛ2)] at h
      have h' := EReal.coe_le_coe_iff.mp h
      nlinarith [mul_le_mul_of_nonneg_left h' hc1.le]
  by_contra hcon
  have hle : B2 ≤ B1 := not_lt.mp hcon
  have hd : 0 < η2 - η1 := by linarith
  have hsum : 0 ≤ (η2 - η1) * (B2 - B1) := by nlinarith
  have hBeq : B1 = B2 := by
    by_contra hne
    have : B2 < B1 := lt_of_le_of_ne hle (Ne.symm hne)
    nlinarith
  have hAeq : A1 = A2 := by
    rw [hBeq] at hI1 hI2; linarith
  -- X1 is then optimal at Λ2, hence equal to X2
  have hV : V P α u u0 Λ2 X1 B0 = V P α u u0 Λ2 X2 B0 := by
    rw [hVc Λ2 X1 (hEu Λ1 hΛ1), hVc Λ2 X2 (hEu Λ2 hΛ2)]
    have e1 := hid η2 hη2 X1 (hEu Λ1 hΛ1)
    have e2 := hid η2 hη2 X2 (hEu Λ2 hΛ2)
    rw [hη2Λ] at e1 e2
    have : (1 + (1 + α) * η2) / (1 + α) * (V P α u u0 Λ2 X1 B0).toReal =
        (1 + (1 + α) * η2) / (1 + α) * (V P α u u0 Λ2 X2 B0).toReal := by
      have : A1 + η2 * B1 = A2 + η2 * B2 := by rw [hAeq, hBeq]
      linarith
    rw [mul_right_inj' hc2.ne'] at this
    rw [this]
  have hae : X1 =ᵐ[P] X2 :=
    huniq Λ2 hΛ2 X1 ⟨(hXex Λ1 hΛ1).1, fun Z hZ => ((hXex Λ2 hΛ2).2 Z hZ).trans hV.ge⟩
  have hlm : ((Λ2 : ℝ) : EReal) < lamMax P ρ x0 α u B0 νG νL := by
    have hL : Λ2 < L := h2.2
    rw [hLdef] at hL; unfold lamCap at hL
    split_ifs at hL with hT
    · rw [hT]; exact EReal.coe_lt_top _
    · have hlt : Λ2 < (lamMax P ρ x0 α u B0 νG νL).toReal := lt_of_lt_of_le hL (min_le_right _ _)
      by_cases hb' : lamMax P ρ x0 α u B0 νG νL = ⊥
      · rw [hb'] at hlt; simp at hlt; linarith
      rw [← EReal.coe_toReal hT hb']
      exact EReal.coe_lt_coe_iff.mpr hlt
  exact (proposition_1_furthermore P ρ x0 α u u0 B0 hρ hx0 hα hu hB0 νG νL hνG hνL Xex
    hXex).2 Λ1 Λ2 hΛ1 h12 hlm hae
