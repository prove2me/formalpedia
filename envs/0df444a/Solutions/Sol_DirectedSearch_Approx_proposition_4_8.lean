-- Prove2me | solution 1 for DirectedSearch.Approx.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:20:19.7228+00:00
-- url     : https://prove2.me/submissions/2436b929-1757-4126-89c7-7ca2125bc2e0

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Theorems.Thm_DirectedSearch_Approx_lemma_4_5
import Theorems.Thm_DirectedSearch_Approx_proposition_4_4
import Theorems.Thm_DirectedSearch_Approx_lemma_4_9

set_option linter.unusedSectionVars false

namespace DSA48

open MeasureTheory DirectedSearch.Approx Set

/-! ### Analytic facts about `tailInt` / `tailMass` (continuity and splitting as in the
accepted proof of Lemma 4.5). -/

section core
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

lemma tm_nonneg (τ : ℝ) : 0 ≤ tailMass μ τ := ENNReal.toReal_nonneg

lemma cont_tailInt (hint : Integrable id μ) : Continuous (tailInt μ) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have h : ∀ a : ℝ, ContinuousOn (fun b => ∫ x in Ici b, x ∂μ) (Ici a) := fun a =>
    (hint.integrableOn : IntegrableOn id (Ici a) μ).continuousOn_Ici_primitive_Ici
  exact (h (τ - 1)).continuousAt (Ici_mem_nhds (by linarith))

lemma split (hint : Integrable id μ) {a b : ℝ} (h : a ≤ b) :
    tailInt μ a = tailInt μ b + ∫ x in Ico a b, x ∂μ ∧
    tailMass μ a = tailMass μ b + (μ (Ico a b)).toReal ∧
    a * (μ (Ico a b)).toReal ≤ ∫ x in Ico a b, x ∂μ ∧
    ∫ x in Ico a b, x ∂μ ≤ b * (μ (Ico a b)).toReal := by
  have hU : Ici a = Ico a b ∪ Ici b := (Ico_union_Ici_eq_Ici h).symm
  have hD : Disjoint (Ico a b) (Ici b) :=
    Set.disjoint_left.2 (fun x hx hy => absurd hx.2 (not_lt.2 hy))
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tailInt
    have e := setIntegral_union (μ := μ) (f := fun x : ℝ => x) hD measurableSet_Ici
      (hint.integrableOn) (hint.integrableOn)
    rw [hU]; linarith
  · unfold tailMass
    rw [hU, measure_union hD measurableSet_Ici,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), add_comm]
  · have := setIntegral_mono_on (μ := μ) (s := Ico a b) (f := fun _ => a) (g := fun x => x)
      (integrableOn_const (by simp)) (hint.integrableOn) measurableSet_Ico
      (fun x hx => hx.1)
    simpa [Measure.real, mul_comm] using this
  · have := setIntegral_mono_on (μ := μ) (s := Ico a b) (f := fun x => x) (g := fun _ => b)
      (hint.integrableOn) (integrableOn_const (by simp)) measurableSet_Ico
      (fun x hx => hx.2.le)
    simpa [Measure.real, mul_comm] using this

lemma ti_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tailInt μ x :=
  setIntegral_nonneg measurableSet_Ici (fun u hu => le_trans hx hu)

lemma ti_anti (hint : Integrable id μ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    tailInt μ y ≤ tailInt μ x := by
  obtain ⟨hI, -, hJ, -⟩ := split μ hint hxy
  have : 0 ≤ x * (μ (Ico x y)).toReal := mul_nonneg hx ENNReal.toReal_nonneg
  linarith

lemma tm_anti (hint : Integrable id μ) {x y : ℝ} (hxy : x ≤ y) :
    tailMass μ y ≤ tailMass μ x := by
  obtain ⟨-, hT, -, -⟩ := split μ hint hxy
  have : 0 ≤ (μ (Ico x y)).toReal := ENNReal.toReal_nonneg
  linarith

lemma ti_gap (hint : Integrable id μ) {x y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ y) :
    tailInt μ x ≤ tailInt μ y + y * tailMass μ x := by
  obtain ⟨hI, hT, -, hJ⟩ := split μ hint hxy
  have h1 := tm_nonneg μ y
  have h2 : y * (μ (Ico x y)).toReal ≤ y * tailMass μ x := by
    apply mul_le_mul_of_nonneg_left _ hy; linarith
  linarith

end core

/-- `ρ ≥ 0` and the fixed-point identity `∫_ρ^∞ u dF = ρ (δ + ∫_ρ^∞ dF)`. -/
lemma rho_facts {M W : Type} (mk : Market M W) (hmk : mk.Standing) (m : M) (w : W) :
    0 ≤ rho mk m w ∧
      tailInt (mk.F m w) (rho mk m w) = rho mk m w * (mk.δ + tailMass (mk.F m w) (rho mk m w)) := by
  have := hmk.prob m w; have := hmk.noAtoms m w
  have h := lemma_4_5 (mk.F m w) (hmk.integrable m w) mk.δ hmk.delta_pos
  obtain ⟨⟨τ, hτ0, hτ⟩, hfix, -, -⟩ := h
  have hpos : ∀ x, 0 < mk.δ + tailMass (mk.F m w) x := fun x => by
    have := tm_nonneg (mk.F m w) x; linarith [hmk.delta_pos]
  have e : rho mk m w = sSup (ratio (mk.F m w) mk.δ '' Set.Ici 0) := rfl
  refine ⟨?_, ?_⟩
  · rw [e, ← hτ]; unfold ratio
    exact div_nonneg (ti_nonneg _ hτ0) (hpos τ).le
  · have hf : ratio (mk.F m w) mk.δ (rho mk m w) = rho mk m w := hfix
    unfold ratio at hf
    have := hpos (rho mk m w)
    field_simp at hf
    linarith

/-- One-dimensional fixed point by the intermediate value theorem. -/
lemma ivt_fixed (φ : ℝ → ℝ) (hφ : Continuous φ) (hanti : ∀ x y, 0 ≤ x → x ≤ y → φ y ≤ φ x)
    (h0 : 0 ≤ φ 0) (c : ℝ) (hc : 0 < c) : ∃ t, 0 ≤ t ∧ c * t = φ t := by
  set t1 := φ 0 / c with ht1
  have ht10 : 0 ≤ t1 := div_nonneg h0 hc.le
  have hg : Continuous (fun t => c * t - φ t) := (continuous_const.mul continuous_id).sub hφ
  have hmem : (0 : ℝ) ∈ Icc ((fun t => c * t - φ t) 0) ((fun t => c * t - φ t) t1) := by
    constructor
    · simp only; linarith
    · simp only
      have : c * t1 = φ 0 := by rw [ht1]; field_simp
      linarith [hanti 0 t1 le_rfl ht10]
  obtain ⟨t, ht, htv⟩ := intermediate_value_Icc ht10 hg.continuousOn hmem
  exact ⟨t, ht.1, by simp only at htv; linarith⟩

/-! ### From flows and thresholds to a second-best feasible profile. -/

section flows
variable {M W : Type} [Fintype M] [Fintype W]

theorem profile_of_flows (mk : Market M W) (hmk : mk.Standing) (f : M → W → ℝ)
    (hf : ∀ m w, 0 ≤ f m w) (τM : M → ℝ) (τW : W → ℝ)
    (hE1 : ∀ m, mk.αM m * τM m = ∑ w, f m w * tailInt (mk.F m w) (max (τM m) (τW w)))
    (hE2 : ∀ w, mk.αW w * τW w = ∑ m, f m w * tailInt (mk.F m w) (max (τM m) (τW w)))
    (hC1 : ∀ m, ∑ w, f m w * (mk.δ + tailMass (mk.F m w) (max (τM m) (τW w))) ≤ mk.αM m)
    (hC2 : ∀ w, ∑ m, f m w * (mk.δ + tailMass (mk.F m w) (max (τM m) (τW w))) ≤ mk.αW w) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      sbWelfare mk P = ∑ m, mk.αM m * τM m + ∑ w, mk.αW w * τW w := by
  have hδ := hmk.delta_pos
  set t : M → W → ℝ := fun m w => tailMass (mk.F m w) (max (τM m) (τW w)) with ht
  have ht0 : ∀ m w, 0 ≤ t m w := fun m w => ENNReal.toReal_nonneg
  set eM : M → ℝ := fun m => (mk.αM m - ∑ w, f m w * t m w) / mk.δ with heM
  set eW : W → ℝ := fun w => (mk.αW w - ∑ m, f m w * t m w) / mk.δ with heW
  have keyM : ∀ m, mk.αM m - ∑ w, f m w * t m w =
      (mk.αM m - ∑ w, f m w * (mk.δ + t m w)) + mk.δ * ∑ w, f m w := by
    intro m
    have : ∑ w, f m w * (mk.δ + t m w) = ∑ w, (f m w * t m w + mk.δ * f m w) :=
      Finset.sum_congr rfl (fun w _ => by ring)
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have keyW : ∀ w, mk.αW w - ∑ m, f m w * t m w =
      (mk.αW w - ∑ m, f m w * (mk.δ + t m w)) + mk.δ * ∑ m, f m w := by
    intro w
    have : ∑ m, f m w * (mk.δ + t m w) = ∑ m, (f m w * t m w + mk.δ * f m w) :=
      Finset.sum_congr rfl (fun m _ => by ring)
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have heMpos : ∀ m, 0 < eM m := by
    intro m
    apply div_pos _ hδ
    rw [keyM]
    have h1 : 0 ≤ mk.αM m - ∑ w, f m w * (mk.δ + t m w) := by linarith [hC1 m]
    have h2 : 0 ≤ ∑ w, f m w := Finset.sum_nonneg (fun w _ => hf m w)
    rcases h2.lt_or_eq with h2 | h2
    · nlinarith
    · have hx00 : ∀ w, f m w = 0 := fun w =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hf m w)).mp h2.symm w (Finset.mem_univ _)
      simp [hx00, hmk.alphaM_pos m]
  have heWpos : ∀ w, 0 < eW w := by
    intro w
    apply div_pos _ hδ
    rw [keyW]
    have h1 : 0 ≤ mk.αW w - ∑ m, f m w * (mk.δ + t m w) := by linarith [hC2 w]
    have h2 : 0 ≤ ∑ m, f m w := Finset.sum_nonneg (fun m _ => hf m w)
    rcases h2.lt_or_eq with h2 | h2
    · nlinarith
    · have hx00 : ∀ m, f m w = 0 := fun m =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hf m w)).mp h2.symm m (Finset.mem_univ _)
      simp [hx00, hmk.alphaW_pos w]
  have hxiM : ∀ m, (mk.δ + ∑ w, f m w / eM m * t m w) * eM m = mk.αM m := by
    intro m
    have hne := (heMpos m).ne'
    rw [add_mul, Finset.sum_mul]
    have : ∑ w, f m w / eM m * t m w * eM m = ∑ w, f m w * t m w :=
      Finset.sum_congr rfl (fun w _ => by field_simp)
    rw [this]; simp only [heM]; field_simp; ring
  have hxiW : ∀ w, (mk.δ + ∑ m, f m w / eW w * t m w) * eW w = mk.αW w := by
    intro w
    have hne := (heWpos w).ne'
    rw [add_mul, Finset.sum_mul]
    have : ∑ m, f m w / eW w * t m w * eW w = ∑ m, f m w * t m w :=
      Finset.sum_congr rfl (fun m _ => by field_simp)
    rw [this]; simp only [heW]; field_simp; ring
  let P : Profile M W :=
    { lamM := fun m w => f m w / eM m
      lamW := fun w m => f m w / eW w
      tauM := τM
      tauW := τW
      xiM := fun m => ∑ w, f m w / eM m * t m w
      xiW := fun w => ∑ m, f m w / eW w * t m w
      etaM := eM
      etaW := eW }
  refine ⟨P, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro m; exact (hxiM m).symm
  · intro w; exact (hxiW w).symm
  · intro m w
    show eM m * (f m w / eM m) = eW w * (f m w / eW w)
    have h1 := (heMpos m).ne'; have h2 := (heWpos w).ne'
    field_simp
  · intro m
    show ∑ w, f m w / eM m ≤ 1
    rw [← Finset.sum_div, div_le_one (heMpos m)]
    simp only [heM]
    rw [keyM, le_div_iff₀ hδ]
    nlinarith [hC1 m]
  · intro w
    show ∑ m, f m w / eW w ≤ 1
    rw [← Finset.sum_div, div_le_one (heWpos w)]
    simp only [heW]
    rw [keyW, le_div_iff₀ hδ]
    nlinarith [hC2 w]
  · intro m; rfl
  · intro w; rfl
  · intro m
    show τM m = (∑ w, f m w / eM m * tailInt (mk.F m w) (max (τM m) (τW w))) /
      (mk.δ + ∑ w, f m w / eM m * t m w)
    have hne := (heMpos m).ne'
    have hα := (hmk.alphaM_pos m).ne'
    have hden : mk.δ + ∑ w, f m w / eM m * t m w = mk.αM m / eM m := by
      rw [← hxiM m]; field_simp
    have hs : ∑ w, f m w / eM m * tailInt (mk.F m w) (max (τM m) (τW w)) =
        (∑ w, f m w * tailInt (mk.F m w) (max (τM m) (τW w))) / eM m := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [hden, hs, ← hE1 m]
    field_simp
  · intro w
    show τW w = (∑ m, f m w / eW w * tailInt (mk.F m w) (max (τM m) (τW w))) /
      (mk.δ + ∑ m, f m w / eW w * t m w)
    have hne := (heWpos w).ne'
    have hα := (hmk.alphaW_pos w).ne'
    have hden : mk.δ + ∑ m, f m w / eW w * t m w = mk.αW w / eW w := by
      rw [← hxiW w]; field_simp
    have hs : ∑ m, f m w / eW w * tailInt (mk.F m w) (max (τM m) (τW w)) =
        (∑ m, f m w * tailInt (mk.F m w) (max (τM m) (τW w))) / eW w := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hden, hs, ← hE2 w]
    field_simp
  · intro m w; exact div_nonneg (hf m w) (heMpos m).le
  · intro w m; exact div_nonneg (hf m w) (heWpos w).le
  · show (∑ m, ∑ w, eM m * (f m w / eM m) * tailInt (mk.F m w) (max (τM m) (τW w))) +
        ∑ w, ∑ m, eW w * (f m w / eW w) * tailInt (mk.F m w) (max (τM m) (τW w)) = _
    have e1 : ∀ m w, eM m * (f m w / eM m) * tailInt (mk.F m w) (max (τM m) (τW w)) =
        f m w * tailInt (mk.F m w) (max (τM m) (τW w)) := by
      intro m w; have := (heMpos m).ne'; field_simp
    have e2 : ∀ m w, eW w * (f m w / eW w) * tailInt (mk.F m w) (max (τM m) (τW w)) =
        f m w * tailInt (mk.F m w) (max (τM m) (τW w)) := by
      intro m w; have := (heWpos w).ne'; field_simp
    simp only [e1, e2, ← hE1, ← hE2]

end flows

/-! ### Star-shaped market with a single `M`-type. -/

section star
variable {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

lemma sum_single (m : M) (hM : ∀ m' : M, m' = m) (g : M → ℝ) : ∑ m', g m' = g m := by
  rw [Finset.sum_eq_single m (fun b _ hb => absurd (hM b) hb)
    (fun h => absurd (Finset.mem_univ m) h)]

/-- Equilibrium thresholds of a star with fixed flows (the reduction of the paper's
fixed-point system (12) to a one-dimensional equation for `τ_m`). -/
lemma star_eq (mk : Market M W) (hmk : mk.Standing) (m : M) (f : W → ℝ) (hf : ∀ w, 0 ≤ f w)
    (t : W → ℝ) (ht0 : ∀ w, 0 ≤ t w)
    (ht : ∀ w, mk.αW w * t w = f w * tailInt (mk.F m w) (t w)) :
    ∃ (τm : ℝ) (τw : W → ℝ), 0 ≤ τm ∧ (∀ w, max τm (τw w) = max τm (t w)) ∧
      mk.αM m * τm = ∑ w, f w * tailInt (mk.F m w) (max τm (t w)) ∧
      ∀ w, mk.αW w * τw w = f w * tailInt (mk.F m w) (max τm (t w)) := by
  set φ : ℝ → ℝ := fun τ => ∑ w, f w * tailInt (mk.F m w) (max τ (t w)) with hφ
  have hcont : Continuous φ := by
    refine continuous_finset_sum _ (fun w _ => ?_)
    have := hmk.prob m w; have := hmk.noAtoms m w
    exact continuous_const.mul ((cont_tailInt _ (hmk.integrable m w)).comp
      (continuous_id.max continuous_const))
  have hanti : ∀ x y, 0 ≤ x → x ≤ y → φ y ≤ φ x := by
    intro x y hx hxy
    refine Finset.sum_le_sum (fun w _ => ?_)
    have := hmk.prob m w; have := hmk.noAtoms m w
    exact mul_le_mul_of_nonneg_left (ti_anti _ (hmk.integrable m w)
      (le_max_of_le_left hx) (max_le_max hxy le_rfl)) (hf w)
  have h0 : 0 ≤ φ 0 := Finset.sum_nonneg (fun w _ => by
    have := hmk.prob m w; have := hmk.noAtoms m w
    exact mul_nonneg (hf w) (ti_nonneg _ (le_max_of_le_left le_rfl)))
  obtain ⟨τm, hτm0, hτm⟩ := ivt_fixed φ hcont hanti h0 (mk.αM m) (hmk.alphaM_pos m)
  refine ⟨τm, fun w => f w * tailInt (mk.F m w) (max τm (t w)) / mk.αW w, hτm0, ?_, hτm, ?_⟩
  · intro w
    have hα := hmk.alphaW_pos w
    have := hmk.prob m w; have := hmk.noAtoms m w
    show max τm (f w * tailInt (mk.F m w) (max τm (t w)) / mk.αW w) = max τm (t w)
    by_cases h : τm ≤ t w
    · rw [max_eq_right h]
      have : f w * tailInt (mk.F m w) (t w) / mk.αW w = t w := by
        rw [← ht w]; field_simp
      rw [this, max_eq_right h]
    · push Not at h
      rw [max_eq_left h.le]
      have hle : f w * tailInt (mk.F m w) τm / mk.αW w ≤ t w := by
        rw [div_le_iff₀ hα, mul_comm (t w), ht w]
        exact mul_le_mul_of_nonneg_left
          (ti_anti _ (hmk.integrable m w) (ht0 w) h.le) (hf w)
      exact max_eq_left (hle.trans h.le)
  · intro w
    have hα := (hmk.alphaW_pos w).ne'
    field_simp

theorem star_M (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      ∀ Q : FBProfile M W, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 2 * sbWelfare mk P := by
  have hδ := hmk.delta_pos
  obtain ⟨β, hβF, hβopt, n, ws, hinj, hsort, hsat, hzero⟩ := lemma_4_9 mk hmk m hM
  obtain ⟨⟨v, hv1, hv2⟩, -⟩ := proposition_4_4 mk hmk
  set V := ∑ w, rho mk m w * β m w with hV
  have hlp : lpObj mk β = 2 * V := by unfold lpObj; rw [sum_single m hM]
  have hFB : ∀ Q, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 2 * V := by
    intro Q hQ
    have h1 := hv1.2 ⟨Q, hQ, rfl⟩
    obtain ⟨β0, hβ0, hv⟩ := hv2.1
    have := hβopt β0 hβ0
    rw [← hv] at h1; linarith
  suffices h : ∃ P, SecondBestFeasible mk P ∧ V ≤ sbWelfare mk P by
    obtain ⟨P, hP, hPV⟩ := h
    exact ⟨P, hP, fun Q hQ => (hFB Q hQ).trans (by linarith)⟩
  have hαm := hmk.alphaM_pos m
  have hβ0 : ∀ w, 0 ≤ β m w := fun w => hβF.1 m w
  have hβrow : ∑ w, β m w ≤ mk.αM m := hβF.2.1 m
  have hβcol : ∀ w, β m w ≤ mk.αW w := fun w => by
    have := hβF.2.2 w; rwa [sum_single m hM (fun m' => β m' w)] at this
  have hβle : ∀ w, β m w ≤ mk.αM m := fun w =>
    (Finset.single_le_sum (fun w' _ => hβ0 w') (Finset.mem_univ w)).trans hβrow
  have hρ0 : ∀ w, 0 ≤ rho mk m w := fun w => (rho_facts mk hmk m w).1
  have hρI : ∀ w, tailInt (mk.F m w) (rho mk m w) =
      rho mk m w * (mk.δ + tailMass (mk.F m w) (rho mk m w)) := fun w => (rho_facts mk hmk m w).2
  have hD : ∀ w x, 0 < mk.δ + tailMass (mk.F m w) x := fun w x => by
    have := hmk.prob m w; have := hmk.noAtoms m w
    have := tm_nonneg (mk.F m w) x; linarith
  set f : W → ℝ := fun w => β m w / (mk.δ + tailMass (mk.F m w) (rho mk m w)) with hfdef
  have hf0 : ∀ w, 0 ≤ f w := fun w => div_nonneg (hβ0 w) (hD w _).le
  have hfβ : ∀ w, f w * (mk.δ + tailMass (mk.F m w) (rho mk m w)) = β m w := fun w => by
    have := (hD w (rho mk m w)).ne'; simp only [hfdef]; field_simp
  have hfI : ∀ w, f w * tailInt (mk.F m w) (rho mk m w) = rho mk m w * β m w := fun w => by
    rw [hρI w, ← hfβ w]; ring
  have hfz : ∀ w, β m w = 0 → f w = 0 := fun w h => by simp only [hfdef, h, zero_div]
  have hfT : ∀ w, f w * tailMass (mk.F m w) (rho mk m w) ≤ β m w := fun w => by
    rw [← hfβ w]; nlinarith [hf0 w]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no edges: β = 0
    subst hn
    have hb : ∀ w, β m w = 0 := fun w => hzero w (by simp)
    obtain ⟨P, hP, hPw⟩ := profile_of_flows mk hmk (fun _ _ => 0) (fun _ _ => le_rfl)
      (fun _ => 0) (fun _ => 0) (by simp) (by simp) (by simp [(hmk.alphaM_pos _).le])
      (by simp [(hmk.alphaW_pos _).le])
    refine ⟨P, hP, ?_⟩
    rw [hPw]; simp [hV, hb]
  set wn := ws ⟨n - 1, by omega⟩ with hwn
  have hclass : ∀ w, 0 < β m w → w ≠ wn → β m w = mk.αW w ∧ rho mk m wn ≤ rho mk m w := by
    intro w hpos hne
    by_cases hr : w ∈ Set.range ws
    · obtain ⟨i, rfl⟩ := hr
      have hi : i.val + 1 < n := by
        by_contra hcon
        apply hne
        rw [hwn]; congr 1; ext; simp only; omega
      exact ⟨hsat i hi, hsort i ⟨n - 1, by omega⟩ (by rw [Fin.le_def]; simp only; omega)⟩
    · exact absurd (hzero w hr) hpos.ne'
  -- ideal thresholds
  have ht : ∀ w, ∃ tw, 0 ≤ tw ∧ tw ≤ rho mk m w ∧
      mk.αW w * tw = f w * tailInt (mk.F m w) tw ∧ (β m w = mk.αW w → tw = rho mk m w) := by
    intro w
    have := hmk.prob m w; have := hmk.noAtoms m w
    have hαw := hmk.alphaW_pos w
    by_cases hs : β m w = mk.αW w
    · exact ⟨rho mk m w, hρ0 w, le_rfl, by rw [hfI w, hs]; ring, fun _ => rfl⟩
    · obtain ⟨tw, htw0, htw⟩ := ivt_fixed (fun x => f w * tailInt (mk.F m w) x)
        (continuous_const.mul (cont_tailInt _ (hmk.integrable m w)))
        (fun x y hx hxy => mul_le_mul_of_nonneg_left
          (ti_anti _ (hmk.integrable m w) hx hxy) (hf0 w))
        (mul_nonneg (hf0 w) (ti_nonneg _ le_rfl)) (mk.αW w) hαw
      refine ⟨tw, htw0, ?_, htw, fun h => absurd h hs⟩
      by_contra hcon; push Not at hcon
      have h1 : f w * tailInt (mk.F m w) tw ≤ f w * tailInt (mk.F m w) (rho mk m w) :=
        mul_le_mul_of_nonneg_left (ti_anti _ (hmk.integrable m w) (hρ0 w) hcon.le) (hf0 w)
      rw [hfI w] at h1
      have h2 : rho mk m w * β m w ≤ rho mk m w * mk.αW w :=
        mul_le_mul_of_nonneg_left (hβcol w) (hρ0 w)
      nlinarith
  choose t ht0 htρ hteq htsat using ht
  obtain ⟨τm, τw, hτm0, hmax, hE1, hE2⟩ := star_eq mk hmk m f hf0 t ht0 hteq
  by_cases hcase : rho mk m wn ≤ τm
  · -- Case 1: the first-best flows induce a feasible equilibrium
    have hθ : ∀ w, 0 < β m w → rho mk m w ≤ max τm (t w) := by
      intro w hpos
      by_cases hw : w = wn
      · rw [hw]; exact le_max_of_le_left hcase
      · rw [htsat w (hclass w hpos hw).1]; exact le_max_right _ _
    have hterm : ∀ w, f w * (mk.δ + tailMass (mk.F m w) (max τm (t w))) ≤ β m w := by
      intro w
      have := hmk.prob m w; have := hmk.noAtoms m w
      rcases (hβ0 w).lt_or_eq with hpos | hz
      · rw [← hfβ w]
        exact mul_le_mul_of_nonneg_left (by linarith [tm_anti _ (hmk.integrable m w) (hθ w hpos)])
          (hf0 w)
      · rw [hfz w hz.symm, ← hz, zero_mul]
    obtain ⟨P, hP, hPw⟩ := profile_of_flows mk hmk (fun _ w => f w) (fun _ w => hf0 w)
      (fun _ => τm) τw
      (by intro m'; rw [hM m']; simp only [hmax]; exact hE1)
      (by intro w; rw [sum_single m hM]; simp only [hmax]; exact hE2 w)
      (by intro m'; rw [hM m']; simp only [hmax]
          exact (Finset.sum_le_sum (fun w _ => hterm w)).trans hβrow)
      (by intro w; rw [sum_single m hM]; simp only [hmax]; exact (hterm w).trans (hβcol w))
    refine ⟨P, hP, ?_⟩
    rw [hPw, sum_single m hM (fun m' => mk.αM m' * τm)]
    have hsw : ∑ w, mk.αW w * τw w = mk.αM m * τm := by
      rw [hE1]; exact Finset.sum_congr rfl (fun w _ => hE2 w)
    rw [hsw]
    have hper : ∀ w, rho mk m w * β m w ≤
        f w * tailInt (mk.F m w) (max τm (t w)) + τm * β m w := by
      intro w
      have := hmk.prob m w; have := hmk.noAtoms m w
      rcases (hβ0 w).lt_or_eq with hpos | hz
      · by_cases hτ : τm ≤ rho mk m w
        · have : max τm (t w) = rho mk m w :=
            le_antisymm (max_le hτ (htρ w)) (hθ w hpos)
          rw [this, hfI w]; nlinarith [hβ0 w]
        · push Not at hτ
          have : max τm (t w) = τm := max_eq_left ((htρ w).trans hτ.le)
          rw [this, ← hfI w]
          have hg := ti_gap _ (hmk.integrable m w) hτm0 hτ.le
          have := mul_le_mul_of_nonneg_left hg (hf0 w)
          nlinarith [hfT w, hτm0]
      · rw [hfz w hz.symm, ← hz]; simp
    have hsum : V ≤ mk.αM m * τm + τm * ∑ w, β m w := by
      rw [hV, hE1, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun w _ => hper w)
    nlinarith
  · -- Case 2
    push Not at hcase
    have hVsplit : V = (∑ w, if w = wn then 0 else rho mk m w * β m w) +
        rho mk m wn * β m wn := by
      have hsp : ∀ w, rho mk m w * β m w = (if w = wn then 0 else rho mk m w * β m w) +
          (if w = wn then rho mk m w * β m w else 0) := by
        intro w; split_ifs <;> simp
      rw [hV, Finset.sum_congr rfl (fun w _ => hsp w), Finset.sum_add_distrib,
        Finset.sum_ite_eq']
      simp
    by_cases h2 : V ≤ 2 * (rho mk m wn * β m wn)
    · -- Subcase 2(b): keep only the edge to `w_n`
      have := hmk.prob m wn; have := hmk.noAtoms m wn
      set b := min (mk.αM m) (mk.αW wn) with hb
      have hαn := hmk.alphaW_pos wn
      have hb1 : b ≤ mk.αM m := min_le_left _ _
      have hb2 : b ≤ mk.αW wn := min_le_right _ _
      have hb0 : 0 ≤ b := le_min hαm.le hαn.le
      set ρn := rho mk m wn with hρn
      set fs := b / (mk.δ + tailMass (mk.F m wn) ρn) with hfs
      have hfs0 : 0 ≤ fs := div_nonneg hb0 (hD wn _).le
      have hfsb : fs * (mk.δ + tailMass (mk.F m wn) ρn) = b := by
        have := (hD wn ρn).ne'; rw [hfs]; field_simp
      have hfsI : fs * tailInt (mk.F m wn) ρn = ρn * b := by
        rw [hρn, hρI wn, ← hρn, ← hfsb]; ring
      have hmx : max (ρn * b / mk.αM m) (ρn * b / mk.αW wn) = ρn := by
        have h1 : ρn * b / mk.αM m ≤ ρn := by
          rw [div_le_iff₀ hαm]; exact mul_le_mul_of_nonneg_left hb1 (hρ0 wn)
        have h2 : ρn * b / mk.αW wn ≤ ρn := by
          rw [div_le_iff₀ hαn]; exact mul_le_mul_of_nonneg_left hb2 (hρ0 wn)
        apply le_antisymm (max_le h1 h2)
        rcases min_choice (mk.αM m) (mk.αW wn) with h | h
        · rw [← hb] at h; apply le_max_of_le_left; rw [h]; field_simp; rfl
        · rw [← hb] at h; apply le_max_of_le_right; rw [h]; field_simp; rfl
      set g : W → ℝ := fun w => if w = wn then fs else 0 with hg
      set τW' : W → ℝ := fun w => if w = wn then ρn * b / mk.αW wn else 0 with hτW'
      have hgz : ∀ w, w ≠ wn → g w = 0 := fun w hw => by simp [hg, hw]
      have hsumg : ∀ X : W → ℝ, ∑ w, g w * X w = fs * X wn := by
        intro X; simp [hg, ite_mul, Finset.sum_ite_eq']
      obtain ⟨P, hP, hPw⟩ := profile_of_flows mk hmk (fun _ w => g w)
        (fun _ w => by simp only [hg]; split_ifs; exacts [hfs0, le_rfl])
        (fun _ => ρn * b / mk.αM m) τW'
        (by
          intro m'; rw [hM m', hsumg]
          simp only [hτW', if_pos rfl, hmx, hfsI]; field_simp)
        (by
          intro w; rw [sum_single m hM]
          by_cases hw : w = wn
          · subst hw; simp only [hg, hτW', if_pos rfl, hmx, hfsI]; field_simp
          · simp [hg, hτW', hw])
        (by
          intro m'; rw [hM m', hsumg]
          simp only [hτW', if_pos rfl, hmx, hfsb]; exact hb1)
        (by
          intro w; rw [sum_single m hM]
          by_cases hw : w = wn
          · subst hw; simp only [hg, hτW', if_pos rfl, hmx, hfsb]; exact hb2
          · simp [hg, hw, (hmk.alphaW_pos w).le])
      refine ⟨P, hP, ?_⟩
      rw [hPw, sum_single m hM (fun m' => mk.αM m' * (ρn * b / mk.αM m))]
      have hs2 : ∑ w, mk.αW w * τW' w = ρn * b := by
        simp only [hτW', mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
      rw [hs2]
      have hβb : β m wn ≤ b := le_min (hβle wn) (hβcol wn)
      have : ρn * β m wn ≤ ρn * b := mul_le_mul_of_nonneg_left hβb (hρ0 wn)
      have e : mk.αM m * (ρn * b / mk.αM m) = ρn * b := by field_simp
      rw [e]; linarith
    · -- Subcase 2(a): drop `w_n`
      push Not at h2
      set f' : W → ℝ := fun w => if w = wn then 0 else f w with hf'
      set t' : W → ℝ := fun w => if w = wn then 0 else t w with ht'
      have hf'0 : ∀ w, 0 ≤ f' w := fun w => by simp only [hf']; split_ifs; exacts [le_rfl, hf0 w]
      have ht'0 : ∀ w, 0 ≤ t' w := fun w => by simp only [ht']; split_ifs; exacts [le_rfl, ht0 w]
      have ht'eq : ∀ w, mk.αW w * t' w = f' w * tailInt (mk.F m w) (t' w) := fun w => by
        simp only [hf', ht']; split_ifs; simp; exact hteq w
      obtain ⟨τm', τw', hτm'0, hmax', hE1', hE2'⟩ := star_eq mk hmk m f' hf'0 t' ht'0 ht'eq
      have hcmp : τm' ≤ τm := by
        by_contra hcon; push Not at hcon
        have h1 : ∑ w, f' w * tailInt (mk.F m w) (max τm' (t' w)) ≤
            ∑ w, f w * tailInt (mk.F m w) (max τm (t w)) := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          have := hmk.prob m w; have := hmk.noAtoms m w
          by_cases hw : w = wn
          · subst hw
            simp only [hf', ht', if_pos rfl, zero_mul]
            exact mul_nonneg (hf0 _) (ti_nonneg _ (le_max_of_le_left hτm0))
          · simp only [hf', ht', hw, if_false]
            exact mul_le_mul_of_nonneg_left (ti_anti _ (hmk.integrable m w)
              (le_max_of_le_left hτm0) (max_le_max hcon.le le_rfl)) (hf0 w)
        rw [← hE1', ← hE1] at h1
        nlinarith
      have hθ' : ∀ w, w ≠ wn → 0 < β m w → max τm' (t' w) = rho mk m w := by
        intro w hw hpos
        obtain ⟨hs, hρw⟩ := hclass w hpos hw
        simp only [ht', if_neg hw, htsat w hs]
        exact max_eq_right (by linarith)
      have hterm' : ∀ w, f' w * tailInt (mk.F m w) (max τm' (t' w)) =
          if w = wn then 0 else rho mk m w * β m w := by
        intro w
        by_cases hw : w = wn
        · simp [hf', hw]
        · rw [if_neg hw]
          rcases (hβ0 w).lt_or_eq with hpos | hz
          · rw [hθ' w hw hpos]; simp only [hf', if_neg hw]; exact hfI w
          · simp only [hf', if_neg hw]; rw [hfz w hz.symm, ← hz]; simp
      have hterm2' : ∀ w, f' w * (mk.δ + tailMass (mk.F m w) (max τm' (t' w))) ≤ β m w := by
        intro w
        by_cases hw : w = wn
        · simp only [hf', hw, if_pos rfl, zero_mul]; exact hβ0 wn
        · rcases (hβ0 w).lt_or_eq with hpos | hz
          · rw [hθ' w hw hpos]; simp only [hf', if_neg hw]; exact (hfβ w).le
          · simp only [hf', if_neg hw]; rw [hfz w hz.symm, ← hz]; simp
      obtain ⟨P, hP, hPw⟩ := profile_of_flows mk hmk (fun _ w => f' w) (fun _ w => hf'0 w)
        (fun _ => τm') τw'
        (by intro m'; rw [hM m']; simp only [hmax']; exact hE1')
        (by intro w; rw [sum_single m hM]; simp only [hmax']; exact hE2' w)
        (by intro m'; rw [hM m']; simp only [hmax']
            exact (Finset.sum_le_sum (fun w _ => hterm2' w)).trans hβrow)
        (by intro w; rw [sum_single m hM]; simp only [hmax']
            exact (hterm2' w).trans (hβcol w))
      refine ⟨P, hP, ?_⟩
      rw [hPw, sum_single m hM (fun m' => mk.αM m' * τm')]
      have hsw : ∑ w, mk.αW w * τw' w = mk.αM m * τm' := by
        rw [hE1']; exact Finset.sum_congr rfl (fun w _ => hE2' w)
      have hV' : mk.αM m * τm' = ∑ w, if w = wn then 0 else rho mk m w * β m w := by
        rw [hE1']; exact Finset.sum_congr rfl (fun w _ => hterm' w)
      rw [hsw]
      linarith

end star

/-! ### Exchanging the two sides of the market. -/

section swap
variable {M W : Type} [Fintype M] [Fintype W]

def swapMk (mk : Market M W) : Market W M := ⟨mk.δ, mk.αW, mk.αM, fun w m => mk.F m w⟩

def swapP (P : Profile W M) : Profile M W :=
  ⟨P.lamW, P.lamM, P.tauW, P.tauM, P.xiW, P.xiM, P.etaW, P.etaM⟩

def swapQ (Q : FBProfile M W) : FBProfile W M :=
  ⟨Q.lamW, Q.lamM, fun w m => Q.tauMW m w, Q.xiW, Q.xiM, Q.etaW, Q.etaM⟩

lemma standing_swap (mk : Market M W) (hmk : mk.Standing) : (swapMk mk).Standing :=
  ⟨hmk.delta_pos, hmk.alphaW_pos, hmk.alphaM_pos, fun w m => hmk.prob m w,
    fun w m => hmk.noAtoms m w, fun w m => hmk.integrable m w⟩

lemma thr_swap (P : Profile W M) (m : M) (w : W) : thr (swapP P) m w = thr P w m := by
  simp only [thr, swapP, max_comm]

lemma sbf_swap (mk : Market M W) (P : Profile W M) (h : SecondBestFeasible (swapMk mk) P) :
    SecondBestFeasible mk (swapP P) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h2, h1, fun m w => (h3 w m).symm, h5, h4, ?_, ?_, ?_, ?_, fun m w => h11 m w,
    fun w m => h10 w m⟩
  · intro m; rw [show (swapP P).xiM m = P.xiW m from rfl, h7 m]
    exact Finset.sum_congr rfl (fun w _ => by rw [thr_swap]; rfl)
  · intro w; rw [show (swapP P).xiW w = P.xiM w from rfl, h6 w]
    exact Finset.sum_congr rfl (fun m _ => by rw [thr_swap]; rfl)
  · intro m; rw [show (swapP P).tauM m = P.tauW m from rfl, h9 m]
    congr 1
    exact Finset.sum_congr rfl (fun w _ => by rw [thr_swap]; rfl)
  · intro w; rw [show (swapP P).tauW w = P.tauM w from rfl, h8 w]
    congr 1
    exact Finset.sum_congr rfl (fun m _ => by rw [thr_swap]; rfl)

lemma sbW_swap (mk : Market M W) (P : Profile W M) :
    sbWelfare mk (swapP P) = sbWelfare (swapMk mk) P := by
  unfold sbWelfare
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun m _ => by
      rw [thr_swap]; rfl))
  · exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun w _ => by
      rw [thr_swap]; rfl))

lemma fbf_swap (mk : Market M W) (Q : FBProfile M W) (h : FirstBestFeasible mk Q) :
    FirstBestFeasible (swapMk mk) (swapQ Q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h2, h1, fun w m => (h3 m w).symm, h5, h4, h7, h6, h9, h8⟩

lemma fbW_swap (mk : Market M W) (Q : FBProfile M W) :
    fbWelfare (swapMk mk) (swapQ Q) = fbWelfare mk Q := by
  unfold fbWelfare; rw [add_comm]; rfl

end swap

end DSA48

open DirectedSearch.Approx DSA48 in
theorem solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (hstar : Fintype.card M = 1 ∨ Fintype.card W = 1) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      ∀ Q : FBProfile M W, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 2 * sbWelfare mk P := by
  rcases hstar with h | h
  · obtain ⟨m, hm⟩ := Fintype.card_eq_one_iff.mp h
    exact star_M mk hmk m hm
  · obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp h
    obtain ⟨P, hP, hPw⟩ := star_M (swapMk mk) (standing_swap mk hmk) w hw
    refine ⟨swapP P, sbf_swap mk P hP, fun Q hQ => ?_⟩
    rw [← fbW_swap, sbW_swap]
    exact hPw _ (fbf_swap mk Q hQ)
