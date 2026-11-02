-- Prove2me | solution 1 for EndoRefLA.PartialPPE.lamPe_exists_unique
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:20:30.312979+00:00
-- url     : https://prove2.me/submissions/cfbd4725-89b1-47d2-9846-ab3daa89a21d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_proposition_1_furthermore
import Theorems.Thm_EndoRefLA_PartialPPE_rewrite_18_19
import Theorems.Thm_EndoRefLA_PartialPPE_value_continuous
import Theorems.Thm_EndoRefLA_PartialPPE_value_strictMono

namespace EndoRefLA.PartialPPE.LamPeAux

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


end EndoRefLA.PartialPPE.LamPeAux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.LamPeAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (f : ℝ → ℝ) (hf : StrictAnti f) (hfc : Continuous f)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ))
    (c0 : ℝ) (hc0 : c0 ∈ Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) :
    (∃! Λ : ℝ, Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL) ∧ f (V P α u u0 lam (Xex Λ) B0).toReal = c0) ∧
    ∀ Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL), f (V P α u u0 lam (Xex Λ) B0).toReal = c0 →
      Xex Λ ∈ Ycal P ρ x0 α u u0 lam B0 f c0 ∧ ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam (Xex Λ) (Xex Λ) := by
  obtain ⟨hVne, hcont, hcap⟩ := value_continuous P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
    νG νL hνG hνL Xex hXex
  have hmono := value_strictMono P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0 νG νL hνG hνL Xex hXex
  set L := lamCap P ρ x0 α lam u B0 νG νL with hLdef
  set v : ℝ → ℝ := fun Λ => (V P α u u0 lam (Xex Λ) B0).toReal with hvdef
  have hVeq : ∀ Λ : ℝ, 1 ≤ Λ → V P α u u0 lam (Xex Λ) B0 = ((v Λ : ℝ) : EReal) := fun Λ hΛ =>
    (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) (hVne Λ hΛ)).symm
  have hBfin : Ex P (fun ω => uE u u0 (B0 ω)) ≠ ⊥ := hB0.2.2
  have hLle : L ≤ lam := by
    rw [hLdef]; unfold lamCap; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hc0' : c0 ∈ Set.Ioo (f (v lam)) (f (v 1)) := hc0
  have hclu : f (v lam) < f (v 1) := lt_trans hc0'.1 hc0'.2
  -- 1 < L
  have hL1 : 1 < L := by
    by_contra hcon
    push_neg at hcon
    have hlm : lamMax P ρ x0 α u B0 νG νL ≤ ((1 : ℝ) : EReal) := by
      by_cases hT : lamMax P ρ x0 α u B0 νG νL = ⊤
      · exfalso
        have : L = lam := by rw [hLdef]; unfold lamCap; rw [if_pos hT]
        have hl1 : lam = 1 := le_antisymm (this ▸ hcon) hlam
        rw [hl1] at hclu; exact lt_irrefl _ hclu
      · have hL' : L = min lam (lamMax P ρ x0 α u B0 νG νL).toReal := by
          rw [hLdef]; unfold lamCap; rw [if_neg hT]
        rcases le_total lam (lamMax P ρ x0 α u B0 νG νL).toReal with h | h
        · exfalso
          rw [min_eq_left h] at hL'
          have hl1 : lam = 1 := le_antisymm (hL' ▸ hcon) hlam
          rw [hl1] at hclu; exact lt_irrefl _ hclu
        · rw [min_eq_right h] at hL'
          by_cases hb : lamMax P ρ x0 α u B0 νG νL = ⊥
          · rw [hb]; exact bot_le
          rw [← EReal.coe_toReal hT hb]
          exact EReal.coe_le_coe_iff.mpr (hL' ▸ hcon)
    have hae := (proposition_1_furthermore P ρ x0 α u u0 B0 hρ hx0 hα hu hB0 νG νL hνG hνL Xex
      hXex).1 1 lam hlm (hlm.trans (EReal.coe_le_coe_iff.mpr hlam))
    have hv : v 1 = v lam := by
      simp only [hvdef]; rw [V_congr P α u u0 lam hae (Filter.EventuallyEq.refl _ _)]
    rw [hv] at hclu; exact lt_irrefl _ hclu
  have hvL : v L = v lam := by simp only [hvdef]; rw [hcap]
  -- existence by the intermediate value theorem, uniqueness by strict monotonicity
  have hgc : ContinuousOn (fun Λ => f (v Λ)) (Set.Icc 1 L) :=
    hfc.comp_continuousOn (hcont.mono (fun x hx => Set.mem_Ici.mpr hx.1))
  have hex : ∃ Λ ∈ Set.Ioo 1 L, f (v Λ) = c0 := by
    have hmem : c0 ∈ Set.Icc (f (v L)) (f (v 1)) := by
      rw [hvL]; exact ⟨hc0'.1.le, hc0'.2.le⟩
    obtain ⟨Λ, hΛ, hgΛ⟩ := intermediate_value_Icc' hL1.le hgc hmem
    simp only at hgΛ
    refine ⟨Λ, ⟨lt_of_le_of_ne hΛ.1 ?_, lt_of_le_of_ne hΛ.2 ?_⟩, hgΛ⟩
    · intro h; rw [← h] at hgΛ; rw [hgΛ] at hc0'; exact lt_irrefl _ hc0'.2
    · intro h; rw [h, hvL] at hgΛ; rw [hgΛ] at hc0'; exact lt_irrefl _ hc0'.1
  have hinj : ∀ Λ1 ∈ Set.Ioo 1 L, ∀ Λ2 ∈ Set.Ioo 1 L, f (v Λ1) = f (v Λ2) → Λ1 = Λ2 := by
    intro Λ1 h1 Λ2 h2 h12
    rcases lt_trichotomy Λ1 Λ2 with h | h | h
    · exact absurd h12 (ne_of_gt (hf (hmono ⟨h1.1.le, h1.2⟩ ⟨h2.1.le, h2.2⟩ h)))
    · exact h
    · exact absurd h12 (ne_of_lt (hf (hmono ⟨h2.1.le, h2.2⟩ ⟨h1.1.le, h1.2⟩ h)))
  refine ⟨?_, ?_⟩
  · obtain ⟨Λ, hΛ, hgΛ⟩ := hex
    exact ⟨Λ, ⟨hΛ, hgΛ⟩, fun Λ' ⟨hΛ', hg'⟩ => hinj Λ' hΛ' Λ hΛ (hg'.trans hgΛ.symm)⟩
  · intro Λ hΛ hgΛ
    have hΛ1 : 1 ≤ Λ := hΛ.1.le
    have hlam1 : 1 < lam := lt_of_lt_of_le hL1 hLle
    refine ⟨⟨(hXex Λ hΛ1).1, v Λ, hVeq Λ hΛ1, hgΛ.le⟩, ?_⟩
    rintro Y ⟨hF, w, hw, hfw⟩
    have hvw : v Λ ≤ w := by
      rw [← hgΛ] at hfw; exact (StrictAnti.le_iff_ge hf).mp hfw
    have hR := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).1
    obtain ⟨-, -, hsurj⟩ := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).2 hlam1
    obtain ⟨η, hη, hηΛ⟩ := hsurj Λ ⟨hΛ.1, lt_of_lt_of_le hΛ.2 hLle⟩
    have hRs := hR η hη (Xex Λ)
    have hRy := hR η hη Y
    rw [hηΛ] at hRs hRy
    set cη : ℝ := (1 + (1 + α) * η) / (1 + α) with hcη
    have hcpos : 0 < cη := by rw [hcη]; positivity
    have hopt := (hXex Λ hΛ1).2 Y hF
    by_cases hYb : V P α u u0 lam Y Y = ⊥
    · rw [hYb]; exact bot_le
    obtain ⟨t, ht⟩ : ∃ t : ℝ, V P α u u0 lam Y Y = (t : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) hYb).symm⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, Ex P (fun ω => uE u u0 (B0 ω)) = (b : EReal) :=
      ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hBfin).symm⟩
    rw [ht, hw, hb] at hRy
    rw [hVeq Λ hΛ1, hb] at hRs
    have hqb : V P α u u0 Λ Y B0 ≠ ⊥ := by
      intro h
      rw [h, EReal.coe_mul_bot_of_pos hcpos, EReal.bot_add] at hRy
      have : ((t + η * w : ℝ) : EReal) = ⊥ := by rw [← hRy]; norm_cast
      exact EReal.coe_ne_bot _ this
    obtain ⟨q, hq⟩ : ∃ q : ℝ, V P α u u0 Λ Y B0 = (q : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 Λ _ _) hqb).symm⟩
    have hpb : V P α u u0 Λ (Xex Λ) B0 ≠ ⊥ := by
      intro h; rw [h, hq] at hopt; exact EReal.coe_ne_bot _ (le_bot_iff.mp hopt)
    obtain ⟨p, hp⟩ : ∃ p : ℝ, V P α u u0 Λ (Xex Λ) B0 = (p : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 Λ _ _) hpb).symm⟩
    rw [hp] at hRs
    rw [hq] at hRy
    rw [hp, hq] at hopt
    have hqp : q ≤ p := EReal.coe_le_coe_iff.mp hopt
    have hsb : V P α u u0 lam (Xex Λ) (Xex Λ) ≠ ⊥ := by
      intro h; rw [h, EReal.bot_add] at hRs
      have : (⊥ : EReal) = ((cη * p + α / (1 + α) * b : ℝ) : EReal) := by rw [hRs]; norm_cast
      exact EReal.bot_ne_coe _ this
    obtain ⟨s, hs⟩ : ∃ s : ℝ, V P α u u0 lam (Xex Λ) (Xex Λ) = (s : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) hsb).symm⟩
    rw [hs] at hRs
    have hRs' : s + η * v Λ = cη * p + α / (1 + α) * b := by exact_mod_cast hRs
    have hRy' : t + η * w = cη * q + α / (1 + α) * b := by exact_mod_cast hRy
    rw [ht, hs]
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left hqp hcpos.le, mul_le_mul_of_nonneg_left hvw hη.le]
