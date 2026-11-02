-- Prove2me | solution 1 for EndoRefLA.PartialPPE.proposition_1_furthermore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:27:01.680275+00:00
-- url     : https://prove2.me/submissions/15b0b786-c5ff-4356-bea2-4182e3f0fd6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_theorem_1
import Theorems.Thm_EndoRefLA_PartialPPE_proposition_1

namespace EndoRefLA.PartialPPE.P1FAux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Iinv_deriv {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) {b : ℝ} (hb : 0 < b) : Iinv u (deriv u b) = b := by
  have hanti : StrictAntiOn (deriv u) (Set.Ioi 0) :=
    hu.strictConcaveOn.strictAntiOn_deriv (fun x hx =>
      (hu.contDiffOn.differentiableOn (by norm_num) x hx).differentiableAt (Ioi_mem_nhds hx))
  unfold Iinv
  apply IsLeast.csInf_eq
  refine ⟨⟨hb, le_rfl⟩, fun x hx => ?_⟩
  obtain ⟨hx0, hxle⟩ := hx
  by_contra h
  push_neg at h
  exact absurd hxle (not_le.mpr (hanti (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hb) h))


lemma deriv_anti {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) : StrictAntiOn (deriv u) (Set.Ioi 0) :=
  hu.strictConcaveOn.strictAntiOn_deriv (fun x hx =>
    (hu.contDiffOn.differentiableOn (by norm_num) x hx).differentiableAt (Ioi_mem_nhds hx))

lemma Iinv_spec {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) {y : ℝ} (hy : 0 < y) :
    0 < Iinv u y ∧ deriv u (Iinv u y) = y := by
  have hcont : ContinuousOn (deriv u) (Set.Ioi 0) :=
    hu.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨a, ha, ha0⟩ := ((hu.inada_zero.eventually (eventually_gt_atTop y)).and
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] 0)).exists
  obtain ⟨b, hb, hab⟩ := ((hu.inada_top.eventually (gt_mem_nhds hy)).and
    (eventually_gt_atTop a)).exists
  have ha0' : (0:ℝ) < a := ha0
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc' hab.le
    (hcont.mono (fun z hz => lt_of_lt_of_le ha0' hz.1)) ⟨hb.le, ha.le⟩
  have hx0 : 0 < x := lt_of_lt_of_le ha0' hx.1
  rw [← hxy, Iinv_deriv hu hx0]
  exact ⟨hx0, rfl⟩

lemma Iinv_inj {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) {y1 y2 : ℝ} (h1 : 0 < y1) (h2 : 0 < y2)
    (h : Iinv u y1 = Iinv u y2) : y1 = y2 := by
  rw [← (Iinv_spec hu h1).2, ← (Iinv_spec hu h2).2, h]

lemma Iinv_gt {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) {y b : ℝ} (hy : 0 < y) (hb : 0 < b) (h : y < deriv u b) :
    b < Iinv u y := by
  by_contra hle
  push_neg at hle
  have := (deriv_anti hu).antitoneOn (Set.mem_Ioi.mpr (Iinv_spec hu hy).1)
    (Set.mem_Ioi.mpr hb) hle
  rw [(Iinv_spec hu hy).2] at this
  linarith

lemma Iinv_lt {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal}
    (hu : Assumption1 P ρ u u0) {y b : ℝ} (hy : 0 < y) (hb : 0 < b) (h : deriv u b < y) :
    Iinv u y < b := by
  by_contra hle
  push_neg at hle
  have := (deriv_anti hu).antitoneOn (Set.mem_Ioi.mpr hb)
    (Set.mem_Ioi.mpr (Iinv_spec hu hy).1) hle
  rw [(Iinv_spec hu hy).2] at this
  linarith

lemma region3_lt {P : Measure Ω} {ρ : Ω → ℝ} {α : ℝ} {u : ℝ → ℝ} {u0 : EReal} {B0 : Ω → ℝ}
    (hu : Assumption1 P ρ u u0) (hα : 0 < α) {ν Λ : ℝ} (hν : 0 < ν) (hΛ : 1 ≤ Λ) {ω : Ω}
    (hρ : 0 < ρ ω) (hB : 0 < B0 ω)
    (h : ¬ ρ ω ≤ (1 + α * Λ) / (1 + α) * (deriv u (B0 ω) / ν)) :
    Iinv u ((1 + α) / (1 + α * Λ) * ν * ρ ω) < B0 ω := by
  push_neg at h
  have h1 : 0 < 1 + α * Λ := by nlinarith
  have h2 : (0:ℝ) < 1 + α := by linarith
  have hy : 0 < (1 + α) / (1 + α * Λ) * ν * ρ ω := by positivity
  apply Iinv_lt hu hy hB
  have hc : 0 < (1 + α) / (1 + α * Λ) * ν := by positivity
  have := mul_lt_mul_of_pos_left h hc
  have he : (1 + α) / (1 + α * Λ) * ν * ((1 + α * Λ) / (1 + α) * (deriv u (B0 ω) / ν)) =
      deriv u (B0 ω) := by field_simp
  linarith

lemma region1_gt {P : Measure Ω} {ρ : Ω → ℝ} {u : ℝ → ℝ} {u0 : EReal} {B0 : Ω → ℝ}
    (hu : Assumption1 P ρ u u0) {ν : ℝ} (hν : 0 < ν) {ω : Ω}
    (hρ : 0 < ρ ω) (hB : 0 ≤ B0 ω) (h : B0 ω = 0 ∨ ρ ω < deriv u (B0 ω) / ν) :
    B0 ω < Iinv u (ν * ρ ω) := by
  have hy : 0 < ν * ρ ω := by positivity
  rcases eq_or_lt_of_le hB with h0 | hpos
  · rw [← h0]; exact (Iinv_spec hu hy).1
  · rcases h with h | h
    · exact absurd h hpos.ne'
    · apply Iinv_gt hu hy hpos
      rw [lt_div_iff₀ hν] at h; linarith

lemma Xhat_gt {P : Measure Ω} {ρ : Ω → ℝ} {α : ℝ} {u : ℝ → ℝ} {u0 : EReal} {B0 : Ω → ℝ}
    (hu : Assumption1 P ρ u u0) (hα : 0 < α) {ν Λ : ℝ} (hν : 0 < ν) (hΛ : 1 ≤ Λ) {ω : Ω}
    (hρ : 0 < ρ ω) (hB : 0 ≤ B0 ω) (h : B0 ω < Xhat ρ α u B0 ν Λ ω) :
    Xhat ρ α u B0 ν Λ ω = Iinv u (ν * ρ ω) := by
  unfold Xhat at h ⊢
  split_ifs at h ⊢ with h1 h2
  · rfl
  · exact absurd h (lt_irrefl _)
  · exfalso
    push_neg at h1
    have hpos : 0 < B0 ω := lt_of_le_of_ne hB (Ne.symm h1.1)
    exact absurd h (not_lt.mpr (region3_lt hu hα hν hΛ hρ hpos h2).le)

lemma Xhat_lt {P : Measure Ω} {ρ : Ω → ℝ} {α : ℝ} {u : ℝ → ℝ} {u0 : EReal} {B0 : Ω → ℝ}
    (hu : Assumption1 P ρ u u0) {ν Λ : ℝ} (hν : 0 < ν) {ω : Ω}
    (hρ : 0 < ρ ω) (hB : 0 ≤ B0 ω) (h : Xhat ρ α u B0 ν Λ ω < B0 ω) :
    Xhat ρ α u B0 ν Λ ω = Iinv u ((1 + α) / (1 + α * Λ) * ν * ρ ω) := by
  unfold Xhat at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact absurd h (not_lt.mpr (region1_gt hu hν hρ hB h1).le)
  · exact absurd h (lt_irrefl _)
  · rfl

lemma price_le {P : Measure Ω} {ρ : Ω → ℝ} (hρ : IsPricingKernel P ρ) {Y Z : Ω → ℝ}
    (h : ∀ᵐ ω ∂P, Y ω ≤ Z ω) : price P ρ Y ≤ price P ρ Z := by
  unfold price
  apply lintegral_mono_ae
  filter_upwards [h] with ω hω
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hω (hρ.2.1 ω).le)

lemma price_lt {P : Measure Ω} {ρ : Ω → ℝ} (hρ : IsPricingKernel P ρ) {Y Z : Ω → ℝ}
    (hZ : Measurable Z) (hY0 : ∀ ω, 0 ≤ Y ω) (hYfin : price P ρ Y ≠ ⊤)
    (hle : ∀ᵐ ω ∂P, Y ω ≤ Z ω) (hlt : ∃ᵐ ω ∂P, Y ω < Z ω) : price P ρ Y < price P ρ Z := by
  unfold price at hYfin ⊢
  apply lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
    (hρ.1.mul hZ).ennreal_ofReal.aemeasurable hYfin
  · filter_upwards [hle] with ω hω
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hω (hρ.2.1 ω).le)
  · refine hlt.mono fun ω hω => ne_of_lt ?_
    have h1 : ρ ω * Y ω < ρ ω * Z ω := mul_lt_mul_of_pos_left hω (hρ.2.1 ω)
    have h0 : 0 ≤ ρ ω * Y ω := mul_nonneg (hρ.2.1 ω).le (hY0 ω)
    exact (ENNReal.ofReal_lt_ofReal_iff (by show (0:ℝ) < ρ ω * Z ω; linarith)).mpr h1

end EndoRefLA.PartialPPE.P1FAux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.P1FAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    (∀ Λ₁ Λ₂ : ℝ, lamMax P ρ x0 α u B0 νG νL ≤ (Λ₁ : EReal) → lamMax P ρ x0 α u B0 νG νL ≤ (Λ₂ : EReal) →
      Xex Λ₁ =ᵐ[P] Xex Λ₂) ∧
    (∀ Λ₁ Λ₂ : ℝ, 1 ≤ Λ₁ → Λ₁ < Λ₂ → (Λ₂ : EReal) < lamMax P ρ x0 α u B0 νG νL →
      ¬ (Xex Λ₁ =ᵐ[P] Xex Λ₂)) := by
  set LM := lamMax P ρ x0 α u B0 νG νL with hLM
  have PR : ∀ Λ : ℝ, 1 ≤ Λ → _ := fun Λ hΛ =>
    (proposition_1 P ρ x0 α Λ u u0 B0 hρ hx0 hα hΛ hu hB0).2.2 νG νL hνG hνL (Xex Λ) (hXex Λ hΛ)
  have hLM1 : (1 : EReal) ≤ LM := (PR 1 le_rfl).1
  constructor
  · intro Λ1 Λ2 h1 h2
    have hΛ1 : 1 ≤ Λ1 := by exact_mod_cast hLM1.trans h1
    have hΛ2 : 1 ≤ Λ2 := by exact_mod_cast hLM1.trans h2
    obtain ⟨-, A1, B1, C1⟩ := PR Λ1 hΛ1
    obtain ⟨-, A2, B2, C2⟩ := PR Λ2 hΛ2
    rcases lt_trichotomy (price P ρ B0) (ENNReal.ofReal x0) with h | h | h
    · exact ((A1 h).2 h1).trans ((A2 h).2 h2).symm
    · exact ((B1 h).mpr h1).trans ((B2 h).mpr h2).symm
    · exact ((C1 h).2 h1).trans ((C2 h).2 h2).symm
  · intro Λ1 Λ2 h1 h12 h2 hae
    have hΛ2 : 1 ≤ Λ2 := h1.trans h12.le
    obtain ⟨⟨ν1, hν1, -, -, huq1, -⟩, -⟩ := theorem_1 P ρ x0 α Λ1 u u0 B0 hρ hx0 hα h1 hu hB0
    obtain ⟨⟨ν2, hν2, hp2, -, huq2, -⟩, -⟩ := theorem_1 P ρ x0 α Λ2 u u0 B0 hρ hx0 hα hΛ2 hu hB0
    set X := Xex Λ2 with hXdef
    have hXh2 : X =ᵐ[P] Xhat ρ α u B0 ν2 Λ2 := huq2 _ (hXex Λ2 hΛ2)
    have hXh1 : X =ᵐ[P] Xhat ρ α u B0 ν1 Λ1 := hae.symm.trans (huq1 _ (hXex Λ1 h1))
    have hpX : price P ρ X = ENNReal.ofReal x0 := by
      rw [← hp2]; unfold price
      apply lintegral_congr_ae
      filter_upwards [hXh2] with ω hω; rw [hω]
    have hXm : Measurable X := (hXex Λ2 hΛ2).1.1
    have hX0 : ∀ ω, 0 ≤ X ω := (hXex Λ2 hΛ2).1.2.1
    have hXfin : price P ρ X ≠ ⊤ := by rw [hpX]; exact ENNReal.ofReal_ne_top
    have hnot : ¬ LM ≤ (Λ2 : EReal) := not_le.mpr h2
    obtain ⟨-, A2, B2, C2⟩ := PR Λ2 hΛ2
    -- both {X > B0} and {X < B0} are non-null
    have hS : (∃ᵐ ω ∂P, B0 ω < X ω) ∧ (∃ᵐ ω ∂P, X ω < B0 ω) := by
      rcases lt_trichotomy (price P ρ B0) (ENNReal.ofReal x0) with h | h | h
      · constructor
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, X ω ≤ B0 ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          have := price_le hρ hle
          rw [hpX] at this; exact absurd h (not_lt.mpr this)
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, B0 ω ≤ X ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          exact hnot ((A2 h).1.mp hle)
      · have hB0fin : price P ρ B0 ≠ ⊤ := by rw [h]; exact ENNReal.ofReal_ne_top
        constructor
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, X ω ≤ B0 ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          by_cases hf : ∃ᵐ ω ∂P, X ω < B0 ω
          · have := price_lt hρ hB0.1 hX0 hXfin hle hf
            rw [hpX, h] at this; exact lt_irrefl _ this
          · have hle' : ∀ᵐ ω ∂P, B0 ω ≤ X ω := by
              filter_upwards [Filter.not_frequently.mp hf] with ω hω; exact not_lt.mp hω
            have heq : X =ᵐ[P] B0 := by
              filter_upwards [hle, hle'] with ω a b; exact le_antisymm a b
            exact hnot ((B2 h).mp heq)
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, B0 ω ≤ X ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          by_cases hf : ∃ᵐ ω ∂P, B0 ω < X ω
          · have := price_lt hρ hXm hB0.2.1 hB0fin hle hf
            rw [hpX, h] at this; exact lt_irrefl _ this
          · have hle' : ∀ᵐ ω ∂P, X ω ≤ B0 ω := by
              filter_upwards [Filter.not_frequently.mp hf] with ω hω; exact not_lt.mp hω
            have heq : X =ᵐ[P] B0 := by
              filter_upwards [hle, hle'] with ω a b; exact le_antisymm b a
            exact hnot ((B2 h).mp heq)
      · constructor
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, X ω ≤ B0 ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          exact hnot ((C2 h).1.mp hle)
        · by_contra hn
          have hle : ∀ᵐ ω ∂P, B0 ω ≤ X ω := by
            filter_upwards [Filter.not_frequently.mp hn] with ω hω; exact not_lt.mp hω
          have := price_le hρ hle
          rw [hpX] at this; exact absurd h (not_lt.mpr this)
    -- on {X > B0}: ν1 = ν2
    obtain ⟨ω, hω, e1, e2⟩ := (hS.1.and_eventually (hXh1.and hXh2)).exists
    have hρω := hρ.2.1 ω
    have hB := hB0.2.1 ω
    rw [e1] at hω
    have g1 := Xhat_gt hu hα hν1 h1 hρω hB hω
    rw [← e1, e2] at hω
    have g2 := Xhat_gt hu hα hν2 hΛ2 hρω hB hω
    have hνeq : ν1 = ν2 := by
      have := Iinv_inj hu (by positivity) (by positivity)
        (g1.symm.trans (e1.symm.trans (e2.trans g2)))
      exact mul_right_cancel₀ hρω.ne' this
    -- on {X < B0}: (1+α)/(1+αΛ1) = (1+α)/(1+αΛ2)
    obtain ⟨ω', hω', e1', e2'⟩ := (hS.2.and_eventually (hXh1.and hXh2)).exists
    have hρω' := hρ.2.1 ω'
    have hB' := hB0.2.1 ω'
    rw [e1'] at hω'
    have g1' := Xhat_lt (α := α) hu hν1 hρω' hB' hω'
    rw [← e1', e2'] at hω'
    have g2' := Xhat_lt (α := α) hu hν2 hρω' hB' hω'
    have hd1 : 0 < 1 + α * Λ1 := by nlinarith
    have hd2 : 0 < 1 + α * Λ2 := by nlinarith
    have hy := Iinv_inj hu (by positivity) (by positivity)
      (g1'.symm.trans (e1'.symm.trans (e2'.trans g2')))
    rw [hνeq] at hy
    have hc : (1 + α) / (1 + α * Λ1) = (1 + α) / (1 + α * Λ2) := by
      have hk : 0 < ν2 * ρ ω' := by positivity
      have : (1 + α) / (1 + α * Λ1) * (ν2 * ρ ω') = (1 + α) / (1 + α * Λ2) * (ν2 * ρ ω') := by
        rw [← mul_assoc, ← mul_assoc]; exact hy
      exact mul_right_cancel₀ hk.ne' this
    rw [div_eq_div_iff hd1.ne' hd2.ne'] at hc
    have : α * (1 + α) * (Λ2 - Λ1) = 0 := by linarith
    have h3 : α * (1 + α) * (Λ2 - Λ1) > 0 := by
      have : 0 < Λ2 - Λ1 := by linarith
      positivity
    linarith
