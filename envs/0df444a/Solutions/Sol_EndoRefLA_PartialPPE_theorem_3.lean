-- Prove2me | solution 1 for EndoRefLA.PartialPPE.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:12:08.384824+00:00
-- url     : https://prove2.me/submissions/339da58f-65c5-4c88-ad6b-5b05dfcb858b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model
import Theorems.Thm_EndoRefLA_PartialPPE_V_self_eq_Ex
import Theorems.Thm_EndoRefLA_PartialPPE_theorem_1
import Theorems.Thm_EndoRefLA_PartialPPE_proposition_1_furthermore
import Theorems.Thm_EndoRefLA_PartialPPE_theorem_2
import Theorems.Thm_EndoRefLA_PartialPPE_problem_10_iff_16
import Theorems.Thm_EndoRefLA_PartialPPE_rewrite_18_19
import Theorems.Thm_EndoRefLA_PartialPPE_value_continuous
import Theorems.Thm_EndoRefLA_PartialPPE_value_strictMono
import Theorems.Thm_EndoRefLA_PartialPPE_lamPe_exists_unique

namespace EndoRefLA.PartialPPE.Thm3Aux

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

lemma Xhat_one {P : Measure Ω} {ρ : Ω → ℝ} {α : ℝ} {u : ℝ → ℝ} {u0 : EReal} {B0 : Ω → ℝ}
    (hu : Assumption1 P ρ u u0) (hα : 0 < α) (hB0 : ∀ ω, 0 ≤ B0 ω) {ν : ℝ} (hν : 0 < ν)
    (ω : Ω) : Xhat ρ α u B0 ν 1 ω = Iinv u (ν * ρ ω) := by
  have h1 : (1 + α * 1) / (1 + α) = 1 := by rw [mul_one]; exact div_self (by linarith)
  unfold Xhat
  rw [h1, one_mul]
  split_ifs with hA hB
  · rfl
  · push_neg at hA
    have hpos : 0 < B0 ω := lt_of_le_of_ne (hB0 ω) (Ne.symm hA.1)
    have heq : ρ ω = deriv u (B0 ω) / ν := le_antisymm hB hA.2
    rw [heq, mul_div_cancel₀ _ hν.ne', Iinv_deriv hu hpos]
  · have h2 : (1 + α) / (1 + α * 1) = 1 := by rw [mul_one]; exact div_self (by linarith)
    rw [h2, one_mul]

end EndoRefLA.PartialPPE.Thm3Aux

open MeasureTheory Filter Topology EndoRefLA.PartialPPE EndoRefLA.PartialPPE.Thm3Aux

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
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    -- (i) c0 = c̲
    (∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f (f (V P α u u0 lam (Xex lam) B0).toReal)) X ↔
      (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex lam)) ∧
    Xex (lamCap P ρ x0 α lam u B0 νG νL) =ᵐ[P] Xex lam ∧
    -- (ii) c0 ≥ c̄
    (∀ c0 : ℝ, f (V P α u u0 lam (Xex 1) B0).toReal ≤ c0 → ∀ X : Ω → ℝ,
      IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔ (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex 1)) ∧
    (∃ ν : ℝ, 0 < ν ∧ price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0) ∧
    (∀ ν : ℝ, 0 < ν → price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0 →
      Xex 1 =ᵐ[P] fun ω => Iinv u (ν * ρ ω)) ∧
    -- (iii) c̲ < c0 < c̄
    ∃ Λpe : ℝ → ℝ,
      (∀ c0 ∈ Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal),
        Λpe c0 ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL) ∧
        f (V P α u u0 lam (Xex (Λpe c0)) B0).toReal = c0 ∧
        (∀ Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL), f (V P α u u0 lam (Xex Λ) B0).toReal = c0 → Λ = Λpe c0) ∧
        ∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔
          (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex (Λpe c0))) ∧
      StrictAntiOn Λpe (Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) ∧
      ContinuousOn Λpe (Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) ∧
      Tendsto Λpe (𝓝[>] (f (V P α u u0 lam (Xex lam) B0).toReal)) (𝓝 (lamCap P ρ x0 α lam u B0 νG νL)) ∧
      Tendsto Λpe (𝓝[<] (f (V P α u u0 lam (Xex 1) B0).toReal)) (𝓝 1) := by
  -- uniqueness of the optimum of (4) (Theorem 1)
  have huniq : ∀ Λ : ℝ, 1 ≤ Λ → ∀ X, IsOptEx P ρ x0 α u u0 B0 Λ X → X =ᵐ[P] Xex Λ := by
    intro Λ hΛ X hX
    obtain ⟨⟨ν, -, -, -, hu1, -⟩, -⟩ := theorem_1 P ρ x0 α Λ u u0 B0 hρ hx0 hα hΛ hu hB0
    exact (hu1 X hX).trans (hu1 _ (hXex Λ hΛ)).symm
  have hfinΛ : ∀ Λ : ℝ, 1 ≤ Λ → V P α u u0 Λ (Xex Λ) B0 ≠ ⊥ := by
    intro Λ hΛ
    obtain ⟨⟨ν, -, -, -, hu1, hne⟩, -⟩ := theorem_1 P ρ x0 α Λ u u0 B0 hρ hx0 hα hΛ hu hB0
    rwa [V_congr P α u u0 Λ (hu1 _ (hXex Λ hΛ)) (Filter.EventuallyEq.refl _ _)]
  obtain ⟨hVne, hcont, hcap⟩ := value_continuous P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
    νG νL hνG hνL Xex hXex
  have hmono := value_strictMono P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0 νG νL hνG hνL Xex hXex
  set L := lamCap P ρ x0 α lam u B0 νG νL with hLdef
  set v : ℝ → ℝ := fun Λ => (V P α u u0 lam (Xex Λ) B0).toReal with hvdef
  have hVeq : ∀ Λ : ℝ, 1 ≤ Λ → V P α u u0 lam (Xex Λ) B0 = ((v Λ : ℝ) : EReal) := fun Λ hΛ =>
    (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) (hVne Λ hΛ)).symm
  have hBfin : Ex P (fun ω => uE u u0 (B0 ω)) ≠ ⊥ := hB0.2.2
  -- generic characterization of the PPE via (16)
  have hppe : ∀ (c : ℝ) (Xs : Ω → ℝ), Xs ∈ Ycal P ρ x0 α u u0 lam B0 f c →
      (∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c, V P α u u0 lam Y Y ≤ V P α u u0 lam Xs Xs) →
      (∀ X ∈ Ycal P ρ x0 α u u0 lam B0 f c,
        (∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c, V P α u u0 lam Y Y ≤ V P α u u0 lam X X) →
          X =ᵐ[P] Xs) →
      ∀ X, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c) X ↔
        (Feasible P ρ x0 X ∧ X =ᵐ[P] Xs) := by
    intro c Xs hXs hmax huq X
    rw [problem_10_iff_16 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0 f c ⟨Xs, hXs, hmax⟩ X]
    constructor
    · rintro ⟨hX, hXm⟩
      exact ⟨hX.1, huq X hX hXm⟩
    · rintro ⟨hF, hae⟩
      refine ⟨⟨hF, ?_⟩, fun Y hY => ?_⟩
      · rw [V_congr P α u u0 lam hae (Filter.EventuallyEq.refl _ _)]; exact hXs.2
      · rw [V_congr P α u u0 lam hae hae]; exact hmax Y hY
  -- c̲ ≤ c̄
  have hv1l : v 1 ≤ v lam := by
    have h := (hXex lam hlam).2 _ (hXex 1 le_rfl).1
    rw [hVeq 1 le_rfl, hVeq lam hlam] at h
    exact EReal.coe_le_coe_iff.mp h
  have hclu : f (v lam) ≤ f (v 1) := hf.antitone hv1l
  have hLle : L ≤ lam := by
    rw [hLdef]; unfold lamCap; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  ---------------- (i)
  have hkey : ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f (f (v lam)), Y =ᵐ[P] Xex lam := by
    rintro Y ⟨hF, w, hw, hfw⟩
    have h1 : v lam ≤ w := (StrictAnti.le_iff_ge hf).mp hfw
    have h2 := (hXex lam hlam).2 Y hF
    rw [hw, hVeq lam hlam] at h2
    have h3 : w ≤ v lam := EReal.coe_le_coe_iff.mp h2
    have heq : V P α u u0 lam Y B0 = V P α u u0 lam (Xex lam) B0 := by
      rw [hw, hVeq lam hlam, le_antisymm h3 h1]
    exact huniq lam hlam Y ⟨hF, fun Z hZ => ((hXex lam hlam).2 Z hZ).trans heq.ge⟩
  have hXsI : Xex lam ∈ Ycal P ρ x0 α u u0 lam B0 f (f (v lam)) :=
    ⟨(hXex lam hlam).1, v lam, hVeq lam hlam, le_rfl⟩
  have partI := hppe (f (v lam)) (Xex lam) hXsI
    (fun Y hY => by rw [V_congr P α u u0 lam (hkey Y hY) (hkey Y hY)])
    (fun X hX _ => hkey X hX)
  have partI2 : Xex L =ᵐ[P] Xex lam := by
    rw [hLdef]; unfold lamCap
    split_ifs with hT
    · exact Filter.EventuallyEq.refl _ _
    · rcases le_total lam (lamMax P ρ x0 α u B0 νG νL).toReal with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        have hbot : lamMax P ρ x0 α u B0 νG νL ≠ ⊥ := by
          unfold lamMax; split_ifs <;> simp
        have hm : lamMax P ρ x0 α u B0 νG νL = ((lamMax P ρ x0 α u B0 νG νL).toReal : EReal) :=
          (EReal.coe_toReal hT hbot).symm
        exact (proposition_1_furthermore P ρ x0 α u u0 B0 hρ hx0 hα hu hB0 νG νL hνG hνL Xex
          hXex).1 _ _ (le_of_eq hm) (by rw [hm]; exact_mod_cast h)
  ---------------- (ii)
  obtain ⟨⟨ν1, hν1, hprice1, hopt1, huq1, hne1⟩, -⟩ :=
    theorem_1 P ρ x0 α 1 u u0 B0 hρ hx0 hα le_rfl hu hB0
  have hX1hat : Xex 1 =ᵐ[P] Xhat ρ α u B0 ν1 1 := huq1 _ (hXex 1 le_rfl)
  have hE1 : Ex P (fun ω => uE u u0 (Xex 1 ω)) ≠ ⊥ := by
    apply Ex_ne_bot_of_V P hα u u0 1 _ B0
    rwa [V_congr P α u u0 1 hX1hat (Filter.EventuallyEq.refl _ _)]
  have hEmax : ∀ Y, Feasible P ρ x0 Y →
      Ex P (fun ω => uE u u0 (Y ω)) ≤ Ex P (fun ω => uE u u0 (Xex 1 ω)) := by
    intro Y hY
    by_cases hYb : Ex P (fun ω => uE u u0 (Y ω)) = ⊥
    · rw [hYb]; exact bot_le
    have h := (hXex 1 le_rfl).2 Y hY
    rw [V_one_eq P α u u0 Y B0 hYb hBfin, V_one_eq P α u u0 (Xex 1) B0 hE1 hBfin] at h
    have h' := EReal.coe_le_coe_iff.mp h
    rw [← EReal.coe_toReal (Ex_ne_top P _) hYb, ← EReal.coe_toReal (Ex_ne_top P _) hE1]
    apply EReal.coe_le_coe_iff.mpr
    have h'' : (1 + α) * (Ex P (fun ω => uE u u0 (Y ω))).toReal ≤
        (1 + α) * (Ex P (fun ω => uE u u0 (Xex 1 ω))).toReal := by linarith
    exact le_of_mul_le_mul_left h'' (by linarith)
  have VXX : ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) :=
    V_self_eq_Ex P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0
  have partII : ∀ c0 : ℝ, f (v 1) ≤ c0 → ∀ X : Ω → ℝ,
      IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔
        (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex 1) := by
    intro c0 hc0
    have hXs : Xex 1 ∈ Ycal P ρ x0 α u u0 lam B0 f c0 :=
      ⟨(hXex 1 le_rfl).1, v 1, hVeq 1 le_rfl, hc0⟩
    refine hppe c0 (Xex 1) hXs (fun Y hY => by rw [VXX, VXX]; exact hEmax Y hY.1) ?_
    intro X hX hXm
    have h := hXm _ hXs
    rw [VXX, VXX] at h
    have hXb : Ex P (fun ω => uE u u0 (X ω)) ≠ ⊥ := ne_bot_of_le_ne_bot hE1 h
    have heqE := le_antisymm (hEmax X hX.1) h
    have heq : V P α u u0 1 X B0 = V P α u u0 1 (Xex 1) B0 := by
      rw [V_one_eq P α u u0 X B0 hXb hBfin, V_one_eq P α u u0 (Xex 1) B0 hE1 hBfin, heqE]
    exact huniq 1 le_rfl X ⟨hX.1, fun Z hZ => ((hXex 1 le_rfl).2 Z hZ).trans heq.ge⟩
  have T2 := theorem_2 P ρ x0 α 1 u u0 B0 hρ hx0 hα le_rfl hu hB0
  have hXhfun : Xhat ρ α u B0 ν1 1 = fun ω => Iinv u (ν1 * ρ ω) :=
    funext fun ω => Xhat_one hu hα hB0.2.1 hν1 ω
  have partII3 : ∀ ν : ℝ, 0 < ν → price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0 →
      Xex 1 =ᵐ[P] fun ω => Iinv u (ν * ρ ω) := by
    intro ν hν hpν
    have hF : Feasible P ρ x0 (Xhat ρ α u B0 ν1 1) := hopt1.1
    have hp1 : price P ρ (fun ω => Iinv u (ν1 * ρ ω)) = ENNReal.ofReal x0 := by
      rw [← hXhfun]; exact hprice1
    have hppe1 := (T2.2.2 ν1 hν1 hp1 _ hF).mpr (by rw [hXhfun])
    exact hX1hat.trans ((T2.2.2 ν hν hpν _ hF).mp hppe1)
  ---------------- (iii)
  set cl := f (v lam) with hcl
  set cu := f (v 1) with hcu
  have LU : ∀ c (hc : c ∈ Set.Ioo cl cu), _ := fun c hc =>
    lamPe_exists_unique P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0 f hf hfc νG νL hνG hνL
      Xex hXex c hc
  classical
  let Λpe : ℝ → ℝ := fun c =>
    if hc : c ∈ Set.Ioo cl cu then Classical.choose (LU c hc).1.exists
    else if c < cu then 1 else L
  have hspec : ∀ c (hc : c ∈ Set.Ioo cl cu), Λpe c ∈ Set.Ioo 1 L ∧ f (v (Λpe c)) = c := by
    intro c hc
    have := Classical.choose_spec (LU c hc).1.exists
    simp only [Λpe, dif_pos hc]
    exact this
  have hunique : ∀ c (hc : c ∈ Set.Ioo cl cu), ∀ Λ ∈ Set.Ioo 1 L, f (v Λ) = c → Λ = Λpe c :=
    fun c hc Λ hΛ hg => (LU c hc).1.unique ⟨hΛ, hg⟩ (hspec c hc)
  -- uniqueness of the optimum of (16) via the Lagrangian rewrite (18)-(19)
  have huqIII : ∀ c0 (hc0 : c0 ∈ Set.Ioo cl cu), ∀ X ∈ Ycal P ρ x0 α u u0 lam B0 f c0,
      (∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam X X) →
        X =ᵐ[P] Xex (Λpe c0) := by
    intro c0 hc0 X hX hXm
    obtain ⟨hΛ, hgΛ⟩ := hspec c0 hc0
    set Λ := Λpe c0 with hΛdef
    have hΛ1 : 1 ≤ Λ := hΛ.1.le
    have hlam1 : 1 < lam := lt_of_lt_of_le (lt_trans hΛ.1 hΛ.2) hLle
    have hR := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).1
    obtain ⟨-, -, hsurj⟩ := (rewrite_18_19 P ρ x0 α lam u u0 B0 hρ hx0 hα hlam hu hB0).2 hlam1
    obtain ⟨η, hη, hηΛ⟩ := hsurj Λ ⟨hΛ.1, lt_of_lt_of_le hΛ.2 hLle⟩
    have hXsY : Xex Λ ∈ Ycal P ρ x0 α u u0 lam B0 f c0 :=
      ((LU c0 hc0).2 Λ hΛ hgΛ).1
    obtain ⟨hF, w, hw, hfw⟩ := hX
    have hvw : v Λ ≤ w := by
      rw [← hgΛ] at hfw; exact (StrictAnti.le_iff_ge hf).mp hfw
    have hXX := hXm _ hXsY
    have hRs := hR η hη (Xex Λ)
    have hRx := hR η hη X
    rw [hηΛ] at hRs hRx
    set cη : ℝ := (1 + (1 + α) * η) / (1 + α) with hcη
    have hcpos : 0 < cη := by rw [hcη]; positivity
    obtain ⟨b, hb⟩ : ∃ b : ℝ, Ex P (fun ω => uE u u0 (B0 ω)) = (b : EReal) :=
      ⟨_, (EReal.coe_toReal (Ex_ne_top P _) hBfin).symm⟩
    obtain ⟨p, hp⟩ : ∃ p : ℝ, V P α u u0 Λ (Xex Λ) B0 = (p : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 Λ _ _) (hfinΛ Λ hΛ1)).symm⟩
    rw [hb, hp, hVeq Λ hΛ1] at hRs
    rw [hb, hw] at hRx
    have hsb : V P α u u0 lam (Xex Λ) (Xex Λ) ≠ ⊥ := by
      intro h; rw [h, EReal.bot_add] at hRs
      have : (⊥ : EReal) = ((cη * p + α / (1 + α) * b : ℝ) : EReal) := by rw [hRs]; norm_cast
      exact EReal.bot_ne_coe _ this
    obtain ⟨sv, hsv⟩ : ∃ sv : ℝ, V P α u u0 lam (Xex Λ) (Xex Λ) = (sv : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) hsb).symm⟩
    have htb : V P α u u0 lam X X ≠ ⊥ := by
      intro h; rw [h, hsv] at hXX; exact EReal.coe_ne_bot _ (le_bot_iff.mp hXX)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, V P α u u0 lam X X = (t : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 lam _ _) htb).symm⟩
    rw [ht] at hRx
    rw [ht, hsv] at hXX
    have hst : sv ≤ t := EReal.coe_le_coe_iff.mp hXX
    have hqb : V P α u u0 Λ X B0 ≠ ⊥ := by
      intro h
      rw [h, EReal.coe_mul_bot_of_pos hcpos, EReal.bot_add] at hRx
      have : ((t + η * w : ℝ) : EReal) = ⊥ := by rw [← hRx]; norm_cast
      exact EReal.coe_ne_bot _ this
    obtain ⟨q, hq⟩ : ∃ q : ℝ, V P α u u0 Λ X B0 = (q : EReal) :=
      ⟨_, (EReal.coe_toReal (V_ne_top P hα u u0 Λ _ _) hqb).symm⟩
    rw [hq] at hRx
    rw [hsv] at hRs
    have hRs' : sv + η * v Λ = cη * p + α / (1 + α) * b := by exact_mod_cast hRs
    have hRx' : t + η * w = cη * q + α / (1 + α) * b := by exact_mod_cast hRx
    have hpq : p ≤ q := by
      have : cη * p ≤ cη * q := by nlinarith
      exact le_of_mul_le_mul_left this hcpos
    have hopt : IsOptEx P ρ x0 α u u0 B0 Λ X := by
      refine ⟨hF, fun Z hZ => ((hXex Λ hΛ1).2 Z hZ).trans ?_⟩
      rw [hp, hq]; exact EReal.coe_le_coe_iff.mpr hpq
    exact huniq Λ hΛ1 X hopt
  -- strict antitonicity of Λpe
  have hanti : StrictAntiOn Λpe (Set.Ioo cl cu) := by
    intro c1 hc1 c2 hc2 hlt
    by_contra hle
    push_neg at hle
    obtain ⟨h1, g1⟩ := hspec c1 hc1
    obtain ⟨h2, g2⟩ := hspec c2 hc2
    rcases hle.lt_or_eq with h | h
    · have := hf (hmono ⟨h1.1.le, h1.2⟩ ⟨h2.1.le, h2.2⟩ h)
      rw [g1, g2] at this; linarith
    · rw [h, g2] at g1; linarith
  -- the value is strictly increasing on [1, L]
  have hvL : v L = v lam := by simp only [hvdef]; rw [hcap]
  have hvlt : ∀ Λ ∈ Set.Ioo 1 L, v Λ < v lam := by
    intro Λ hΛ
    rw [← hvL]
    set Λ' := (Λ + L) / 2 with hΛ'
    have hΛ'1 : Λ < Λ' := by rw [hΛ']; linarith [hΛ.2]
    have hΛ'2 : Λ' < L := by rw [hΛ']; linarith [hΛ.2]
    have h1 : v Λ < v Λ' := hmono ⟨hΛ.1.le, hΛ.2⟩ ⟨by linarith [hΛ.1], hΛ'2⟩ hΛ'1
    have hL1 : (1 : ℝ) ≤ L := by linarith [hΛ.1, hΛ.2]
    have hcw : ContinuousWithinAt v (Set.Iio L) L :=
      (hcont L hL1).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsLT (by linarith [hΛ.1, hΛ.2] : (1:ℝ) < L))
          (fun x hx => Set.mem_Ici.mpr hx.1.le))
    have h2 : v Λ' ≤ v L := by
      refine ge_of_tendsto hcw.tendsto ?_
      filter_upwards [Ioo_mem_nhdsLT hΛ'2] with t ht
      exact (hmono ⟨by linarith [hΛ.1], hΛ'2⟩ ⟨by linarith [hΛ.1, ht.1], ht.2⟩ ht.1).le
    linarith
  have hgmem : ∀ Λ ∈ Set.Ioo 1 L, f (v Λ) ∈ Set.Ioo cl cu := by
    intro Λ hΛ
    refine ⟨hf (hvlt Λ hΛ), hf (hmono ⟨le_rfl, by linarith [hΛ.1, hΛ.2]⟩ ⟨hΛ.1.le, hΛ.2⟩ hΛ.1)⟩
  have hinv : ∀ Λ ∈ Set.Ioo 1 L, Λpe (f (v Λ)) = Λ := fun Λ hΛ =>
    (hunique _ (hgmem Λ hΛ) Λ hΛ rfl).symm
  refine ⟨partI, partI2, partII, T2.2.1, partII3, Λpe, ?_, hanti, ?_, ?_, ?_⟩
  · intro c0 hc0
    obtain ⟨hΛ, hgΛ⟩ := hspec c0 hc0
    refine ⟨hΛ, hgΛ, hunique c0 hc0, ?_⟩
    obtain ⟨hXs, hmax⟩ := (LU c0 hc0).2 _ hΛ hgΛ
    exact hppe c0 _ hXs hmax (huqIII c0 hc0)
  · -- continuity
    intro c hc
    apply ContinuousAt.continuousWithinAt
    have hmn : MonotoneOn (fun c => -Λpe c) (Set.Ioo cl cu) :=
      fun a ha b hb hab => neg_le_neg (hanti.antitoneOn ha hb hab)
    have hca : ContinuousAt (fun c => -Λpe c) c := by
      apply continuousAt_of_monotoneOn_of_image_mem_nhds hmn (Ioo_mem_nhds hc.1 hc.2)
      obtain ⟨hΛ, -⟩ := hspec c hc
      refine mem_of_superset (Ioo_mem_nhds (a := -L) (b := -1) (by linarith [hΛ.2])
        (by linarith [hΛ.1])) ?_
      intro y hy
      refine ⟨f (v (-y)), hgmem (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
      simp only
      rw [hinv (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_neg]
    convert hca.neg using 1
    funext x; simp
  · -- limit at c̲
    rcases hclu.lt_or_eq with hlt | heq
    · obtain ⟨hΛm, -⟩ := hspec ((cl + cu) / 2) ⟨by linarith, by linarith⟩
      have h1L : 1 < L := lt_trans hΛm.1 hΛm.2
      rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · set Λ := (max a 1 + L) / 2 with hΛ
        have hm : max a 1 < L := max_lt ha h1L
        have hΛI : Λ ∈ Set.Ioo 1 L := ⟨by rw [hΛ]; linarith [le_max_right a 1],
          by rw [hΛ]; linarith⟩
        have hcs := hgmem Λ hΛI
        filter_upwards [Ioo_mem_nhdsGT hcs.1] with c hc
        have hcI : c ∈ Set.Ioo cl cu := ⟨hc.1, lt_trans hc.2 hcs.2⟩
        have := hanti hcI hcs hc.2
        rw [hinv Λ hΛI] at this
        have : a < Λ := by rw [hΛ]; linarith [le_max_left a 1]
        linarith
      · filter_upwards [Ioo_mem_nhdsGT hlt] with c hc
        exact lt_trans (hspec c hc).1.2 ha
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with c (hc : cl < c)
      have h1 : c ∉ Set.Ioo cl cu := fun h => by linarith [h.2]
      have h2 : ¬ c < cu := by linarith
      simp only [Λpe, dif_neg h1, if_neg h2]
  · -- limit at c̄
    rcases hclu.lt_or_eq with hlt | heq
    · obtain ⟨hΛm, -⟩ := hspec ((cl + cu) / 2) ⟨by linarith, by linarith⟩
      have h1L : 1 < L := lt_trans hΛm.1 hΛm.2
      rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · filter_upwards [Ioo_mem_nhdsLT hlt] with c hc
        exact lt_trans ha (hspec c hc).1.1
      · set Λ := (1 + min a L) / 2 with hΛ
        have hm : 1 < min a L := lt_min ha h1L
        have hΛI : Λ ∈ Set.Ioo 1 L := ⟨by rw [hΛ]; linarith,
          by rw [hΛ]; linarith [min_le_right a L]⟩
        have hcs := hgmem Λ hΛI
        filter_upwards [Ioo_mem_nhdsLT hcs.2] with c hc
        have hcI : c ∈ Set.Ioo cl cu := ⟨lt_trans hcs.1 hc.1, hc.2⟩
        have := hanti hcs hcI hc.1
        rw [hinv Λ hΛI] at this
        have : Λ < a := by rw [hΛ]; linarith [min_le_left a L]
        linarith
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with c (hc : c < cu)
      have h1 : c ∉ Set.Ioo cl cu := fun h => by linarith [h.1]
      simp only [Λpe, dif_neg h1, if_pos hc]

