-- Prove2me | solution 1 for CappeKLUCB.ExpFam.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:35:32.510241+00:00
-- url     : https://prove2.me/submissions/cf6726d8-5123-4d15-81c3-5649854a465b

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

namespace CappeKLUCB.ExpFam

/-- In the initialization rounds `1..K` an index run plays each arm at most once. -/
lemma init_card_le_one {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (a : Fin K) (ω : Ω) :
    ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_range] at hx hy
  by_contra hne
  have key : ∀ x y, x < K → y < K → I (x + 1) ω = a → I (y + 1) ω = a → x < y → False := by
    intro x y hxK hyK hxa hya hxy
    have h0 := (hrun ω y).1 hyK
    unfold pullCount at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_range.mpr hxy) (by rw [hxa, hya])
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y hx.1 hy.1 hx.2 hy.2 h
  · exact key y x hy.1 hx.1 hy.2 hx.2 h

lemma pullCount_le_init_add {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (a : Fin K) (T : ℕ) (ω : Ω) :
    (pullCount I a T ω : ℝ) ≤
      1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω := by
  have hsub : (Finset.range T).filter (fun s => I (s + 1) ω = a) ⊆
      (Finset.range K).filter (fun s => I (s + 1) ω = a) ∪
        (Finset.Ico K T).filter (fun s => I (s + 1) ω = a) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hs ⊢
    by_cases hsK : s < K
    · exact Or.inl ⟨hsK, hs.2⟩
    · exact Or.inr ⟨⟨by omega, hs.1⟩, hs.2⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := init_card_le_one hrun a ω
  have h3 : (((Finset.Ico K T).filter (fun s => I (s + 1) ω = a)).card : ℝ) =
      ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [Set.indicator_apply]
  have h4 : (pullCount I a T ω : ℝ) ≤ (((Finset.range K).filter (fun s => I (s + 1) ω = a)).card : ℝ)
      + (((Finset.Ico K T).filter (fun s => I (s + 1) ω = a)).card : ℝ) := by
    unfold pullCount; exact_mod_cast h1
  have h5 : (((Finset.range K).filter (fun s => I (s + 1) ω = a)).card : ℝ) ≤ 1 := by
    exact_mod_cast h2
  linarith

theorem eds_aux {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a astar : Fin K) (hastar : μ astar = bestMean μ)
    (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      1 + ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag}
        + ∑ t ∈ Finset.Ico K T,
            P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} := by
  have hms : ∀ t, MeasurableSet {ω | I (t + 1) ω = a} := fun t =>
    (hI (t + 1)) (measurableSet_singleton a)
  have hint : ∀ t, Integrable (Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ)) P := fun t =>
    (integrable_const (1 : ℝ)).indicator (hms t)
  have hmono : ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      ∫ ω, (1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => by positivity)) ?_
      (Filter.Eventually.of_forall (fun ω => pullCount_le_init_add hrun a T ω))
    exact (integrable_const 1).add (integrable_finsetSum _ (fun t _ => hint t))
  have heq : ∫ ω, (1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω) ∂P
      = 1 + ∑ t ∈ Finset.Ico K T, P.real {ω | I (t + 1) ω = a} := by
    rw [integral_add (integrable_const 1) (integrable_finsetSum _ (fun t _ => hint t)),
      integral_finsetSum _ (fun t _ => hint t)]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact integral_indicator_one (hms t)
  have hpt : ∀ t ∈ Finset.Ico K T, P.real {ω | I (t + 1) ω = a} ≤
      P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag} +
        P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} := by
    intro t ht
    have hKt : K ≤ t := (Finset.mem_Ico.mp ht).1
    have hsub : {ω | I (t + 1) ω = a} ⊆ {ω | klucbIndex F f₁ X I astar t ω ≤ μdag} ∪
        {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_cases hc : klucbIndex F f₁ X I astar t ω ≤ μdag
      · exact Or.inl hc
      · right
        refine ⟨?_, hω⟩
        have hmax := (hrun ω t).2 hKt astar
        rw [hω] at hmax
        push Not at hc
        exact lt_of_lt_of_le hc hmax
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  linarith [hmono, heq, hsum]



lemma expFam_convex (F : ExpFamily) : Convex ℝ F.Θ :=
  F.ordConnected_Θ.convex

lemma expFam_diffAt (F : ExpFamily) {x : ℝ} (hx : x ∈ F.Θ) : DifferentiableAt ℝ F.b x :=
  (F.contDiff.differentiableOn (by norm_num)).differentiableAt (F.isOpen_Θ.mem_nhds hx)

lemma expFam_deriv_strictMono (F : ExpFamily) : StrictMonoOn (deriv F.b) F.Θ := by
  apply strictMonoOn_of_deriv_pos (expFam_convex F)
    (F.contDiff.continuousOn_deriv_of_isOpen F.isOpen_Θ (by norm_num))
  intro x hx
  rw [F.isOpen_Θ.interior_eq] at hx
  exact F.deriv2_pos x hx

/-- Tangent-line bound: `b φ ≥ b ψ + ḃ ψ (φ - ψ)` for `ψ ≤ φ` in `Θ`. -/
lemma expFam_tangent (F : ExpFamily) {ψ φ : ℝ} (hψ : ψ ∈ F.Θ) (hφ : φ ∈ F.Θ) (h : ψ ≤ φ) :
    F.b ψ + deriv F.b ψ * (φ - ψ) ≤ F.b φ := by
  set D := F.Θ ∩ Set.Ici ψ with hD
  have hDc : Convex ℝ D := (expFam_convex F).inter (convex_Ici ψ)
  have hsub : D ⊆ F.Θ := Set.inter_subset_left
  have hcont : ContinuousOn (fun x => F.b x - deriv F.b ψ * x) D :=
    (F.contDiff.continuousOn.mono hsub).sub (continuousOn_const.mul continuousOn_id)
  have hint : ∀ x ∈ interior D, x ∈ D := fun x hx => interior_subset hx
  have hdiff : DifferentiableOn ℝ (fun x => F.b x - deriv F.b ψ * x) (interior D) := by
    intro x hx
    exact ((expFam_diffAt F (hsub (hint x hx))).sub
      ((differentiableAt_id).const_mul _)).differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg hDc hcont hdiff (by
    intro x hx
    have hxD := hint x hx
    have hd : deriv (fun x => F.b x - deriv F.b ψ * x) x = deriv F.b x - deriv F.b ψ := by
      have h : HasDerivAt (fun x => F.b x - deriv F.b ψ * x) (deriv F.b x - deriv F.b ψ * 1) x :=
        (expFam_diffAt F (hsub hxD)).hasDerivAt.sub ((hasDerivAt_id x).const_mul (deriv F.b ψ))
      rw [h.deriv, mul_one]
    rw [hd, sub_nonneg]
    exact (expFam_deriv_strictMono F).monotoneOn hψ (hsub hxD) hxD.2)
  have := hmono ⟨hψ, (Set.mem_Ici.mpr le_rfl)⟩ ⟨hφ, h⟩ h
  simp only at this
  nlinarith

lemma expFam_lintegral_exp (F : ExpFamily) {ψ : ℝ} (hψ : ψ ∈ F.Θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (ψ * x)) ∂F.ξ = ENNReal.ofReal (Real.exp (F.b ψ)) := by
  have h1 := F.isNormalized ψ hψ
  have heq : (fun x => ENNReal.ofReal (Real.exp (ψ * x))) =
      fun x => ENNReal.ofReal (Real.exp (ψ * x - F.b ψ)) * ENNReal.ofReal (Real.exp (F.b ψ)) := by
    funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [heq, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, h1, one_mul]

/-- Under `IsNatural`, if `Θ ∩ [θ₁, ∞)` is bounded above then `b` is unbounded on it. -/
lemma expFam_b_unbdd (F : ExpFamily) (hnat : IsNatural F) {θ1 : ℝ} (hθ1 : θ1 ∈ F.Θ)
    (hbdd : BddAbove (F.Θ ∩ Set.Ici θ1)) (B : ℝ) :
    ∃ ψ ∈ F.Θ, θ1 ≤ ψ ∧ B < F.b ψ := by
  by_contra hcon
  push Not at hcon
  set s := sSup (F.Θ ∩ Set.Ici θ1) with hs
  have hne : (F.Θ ∩ Set.Ici θ1).Nonempty := ⟨θ1, hθ1, Set.mem_Ici.mpr le_rfl⟩
  have hθ1s : θ1 ≤ s := le_csSup hbdd ⟨hθ1, (Set.mem_Ici.mpr le_rfl)⟩
  have hsnot : s ∉ F.Θ := by
    intro hsΘ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp F.isOpen_Θ s hsΘ
    have hmem : s + ε / 2 ∈ F.Θ ∩ Set.Ici θ1 := by
      refine ⟨hball ?_, by simp only [Set.mem_Ici]; linarith⟩
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_pos (by linarith)]
      linarith
    have := le_csSup hbdd hmem
    linarith
  have hlt : θ1 < s := lt_of_le_of_ne hθ1s (fun h => hsnot (h ▸ hθ1))
  -- every ψ ∈ (θ1, s) lies in Θ
  have hin : ∀ ψ, θ1 < ψ → ψ < s → ψ ∈ F.Θ := by
    intro ψ h1 h2
    obtain ⟨e, he, hψe⟩ := exists_lt_of_lt_csSup hne h2
    exact F.ordConnected_Θ.out hθ1 he.1 ⟨h1.le, hψe.le⟩
  -- Fatou along ψ → s⁻
  have hfatou := lintegral_liminf_le (μ := F.ξ) (u := nhdsWithin s (Set.Iio s))
    (f := fun ψ x => ENNReal.ofReal (Real.exp (ψ * x)))
    (fun ψ => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul ψ)))
  have hpt : ∀ x, Filter.liminf (fun ψ => ENNReal.ofReal (Real.exp (ψ * x)))
      (nhdsWithin s (Set.Iio s)) = ENNReal.ofReal (Real.exp (s * x)) := by
    intro x
    apply Filter.Tendsto.liminf_eq
    have hc : Continuous (fun ψ : ℝ => ENNReal.ofReal (Real.exp (ψ * x))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.mul continuous_const))
    exact (hc.tendsto s).mono_left nhdsWithin_le_nhds
  simp only [hpt] at hfatou
  have hev : ∀ᶠ ψ in nhdsWithin s (Set.Iio s),
      ∫⁻ x, ENNReal.ofReal (Real.exp (ψ * x)) ∂F.ξ ≤ ENNReal.ofReal (Real.exp B) := by
    filter_upwards [Ioo_mem_nhdsLT hlt] with ψ hψ
    have hψΘ := hin ψ hψ.1 hψ.2
    rw [expFam_lintegral_exp F hψΘ]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcon ψ hψΘ hψ.1.le))
  have hlim : Filter.liminf (fun ψ => ∫⁻ x, ENNReal.ofReal (Real.exp (ψ * x)) ∂F.ξ)
      (nhdsWithin s (Set.Iio s)) ≤ ENNReal.ofReal (Real.exp B) :=
    Filter.liminf_le_of_frequently_le' hev.frequently
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂F.ξ < ⊤ :=
    lt_of_le_of_lt (hfatou.trans hlim) ENNReal.ofReal_lt_top
  apply hsnot
  rw [hnat]
  exact hfin

/-- The set defining `klIndex` is bounded above (needs `IsNatural`). -/
lemma klIndex_bdd (F : ExpFamily) (hnat : IsNatural F) (m γ : ℝ) :
    BddAbove ({μ ∈ F.M | dExt F m μ ≤ ENNReal.ofReal γ} ∪ {m}) := by
  classical
  by_cases hA : ∀ φ ∈ F.Θ, deriv F.b φ ≤ m
  · refine ⟨m, ?_⟩
    rintro x (⟨⟨φ, hφ, rfl⟩, _⟩ | hx)
    · exact hA φ hφ
    · rw [Set.mem_singleton_iff] at hx; rw [hx]
  push Not at hA
  obtain ⟨θ1, hθ1, hm1⟩ := hA
  set C := max γ 0 + (F.b θ1 - θ1 * m) with hC
  -- g φ := b φ - φ m is nondecreasing on Θ ∩ [θ1, ∞)
  have hgmono : ∀ ψ φ, ψ ∈ F.Θ → φ ∈ F.Θ → θ1 ≤ ψ → ψ ≤ φ →
      F.b ψ - ψ * m ≤ F.b φ - φ * m := by
    intro ψ φ hψ hφ h1 h2
    have ht := expFam_tangent F hψ hφ h2
    have hd : deriv F.b θ1 ≤ deriv F.b ψ := (expFam_deriv_strictMono F).monotoneOn hθ1 hψ h1
    nlinarith
  -- some ψ ≥ θ1 in Θ has g ψ > C
  obtain ⟨ψ, hψΘ, hψ1, hgψ⟩ : ∃ ψ ∈ F.Θ, θ1 ≤ ψ ∧ C < F.b ψ - ψ * m := by
    by_contra hcon
    push Not at hcon
    have hc : 0 < deriv F.b θ1 - m := by linarith
    set φs := θ1 + max γ 0 / (deriv F.b θ1 - m) with hφs
    have hbdd : BddAbove (F.Θ ∩ Set.Ici θ1) := by
      refine ⟨φs, ?_⟩
      rintro φ ⟨hφ, hφ1⟩
      have ht := expFam_tangent F hθ1 hφ hφ1
      have hg := hcon φ hφ hφ1
      rw [hφs, ← sub_le_iff_le_add', le_div_iff₀ hc]
      nlinarith
    obtain ⟨φ, hφ, hφ1, hbig⟩ := expFam_b_unbdd F hnat hθ1 hbdd (C + |θ1 * m| + |φs * m|)
    have hg := hcon φ hφ hφ1
    have hφle : φ ≤ φs := by
      have ht := expFam_tangent F hθ1 hφ hφ1
      rw [hφs, ← sub_le_iff_le_add', le_div_iff₀ hc]
      nlinarith
    have hφm : φ * m ≤ |θ1 * m| + |φs * m| := by
      rcases le_total 0 m with hm | hm
      · have : φ * m ≤ φs * m := mul_le_mul_of_nonneg_right hφle hm
        linarith [le_abs_self (φs * m), abs_nonneg (θ1 * m)]
      · have : φ * m ≤ θ1 * m := mul_le_mul_of_nonpos_right hφ1 hm
        linarith [le_abs_self (θ1 * m), abs_nonneg (φs * m)]
    linarith
  refine ⟨max m (deriv F.b ψ), ?_⟩
  rintro x (⟨hxM, hxd⟩ | hx)
  · have hφΘ : F.θof x ∈ F.Θ := Function.invFunOn_mem hxM
    have hφx : deriv F.b (F.θof x) = x := Function.invFunOn_eq hxM
    have h1 : ENNReal.ofReal ((θ1 - F.θof x) * m - F.b θ1 + F.b (F.θof x)) ≤ dExt F m x :=
      le_iSup (fun θ : F.Θ => ENNReal.ofReal (((θ : ℝ) - F.θof x) * m - F.b θ + F.b (F.θof x)))
        ⟨θ1, hθ1⟩
    have h2 := (h1.trans hxd)
    rw [ENNReal.ofReal_le_ofReal_iff'] at h2
    have hgφ : F.b (F.θof x) - F.θof x * m ≤ C := by
      rcases h2 with h2 | h2
      · rw [hC]; nlinarith [le_max_left γ 0]
      · rw [hC]; nlinarith [le_max_right γ 0]
    have hle : F.θof x ≤ ψ := by
      by_contra hgt
      push Not at hgt
      have := hgmono ψ (F.θof x) hψΘ hφΘ hψ1 hgt.le
      linarith
    rw [← hφx]
    exact le_max_of_le_right ((expFam_deriv_strictMono F).monotoneOn hφΘ hψΘ hle)
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact le_max_left _ _


lemma klIndex_mono (F : ExpFamily) (hnat : IsNatural F) (m : ℝ) {γ γ' : ℝ} (h : γ ≤ γ') :
    klIndex F m γ ≤ klIndex F m γ' := by
  unfold klIndex
  apply csSup_le_csSup (klIndex_bdd F hnat m γ') ⟨m, Or.inr rfl⟩
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.1, hx.2.trans (ENNReal.ofReal_le_ofReal h)⟩
  · exact Or.inr hx

lemma f₁_mono {t T : ℕ} (h : t ≤ T) : f₁ t ≤ f₁ T := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : ∀ x y : ℝ, 3 ≤ x → x ≤ y →
      Real.log x + 3 * Real.log (Real.log x) ≤ Real.log y + 3 * Real.log (Real.log y) := by
    intro x y hx hxy
    have h1 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
    have h2 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h3 : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
      Real.log_le_log (by linarith) h1
    linarith
  unfold f₁
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact key 3 T le_rfl (le_of_lt (by exact_mod_cast (by omega : 3 < T)))
  · omega
  · exact key t T (le_of_lt (by exact_mod_cast (by omega : 3 < t)))
      (by exact_mod_cast h)

lemma init_injOn {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (ω : Ω) :
    Set.InjOn (fun s => I (s + 1) ω) (Finset.range K : Set ℕ) := by
  have key : ∀ x y, y < K → I (x + 1) ω = I (y + 1) ω → x < y → False := by
    intro x y hyK hxy hlt
    have h0 := (hrun ω y).1 hyK
    unfold pullCount at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_range.mpr hlt) hxy
  intro x hx y hy hxy
  simp only [Finset.coe_range, Set.mem_Iio] at hx hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y hy hxy h
  · exact key y x hx hxy.symm h

lemma init_card_eq_one {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (a : Fin K) (ω : Ω) :
    ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card = 1 := by
  have h1 := init_card_le_one hrun a ω
  have hsurj : (Finset.range K).image (fun s => I (s + 1) ω) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (init_injOn hrun ω), Finset.card_range, Fintype.card_fin]
  have hmem : a ∈ (Finset.range K).image (fun s => I (s + 1) ω) := by
    rw [hsurj]; exact Finset.mem_univ a
  obtain ⟨s, hs, hsa⟩ := Finset.mem_image.mp hmem
  have h2 : 0 < ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card :=
    Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hsa⟩⟩
  omega

lemma pullCount_eq_init_add {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (a : Fin K) (t : ℕ) (hKt : K ≤ t) (ω : Ω) :
    pullCount I a t ω = 1 + ((Finset.Ico K t).filter (fun s => I (s + 1) ω = a)).card := by
  unfold pullCount
  have hr : Finset.range t = Finset.range K ∪ Finset.Ico K t := by
    ext s; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [hr, Finset.filter_union, Finset.card_union_of_disjoint, init_card_eq_one hrun a ω]
  rw [Finset.disjoint_left]
  intro s h1 h2
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h1 h2
  omega

lemma pullCount_bounds {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : IsIndexRun U I) (a : Fin K) (t : ℕ) (hKt : K ≤ t) (ω : Ω) :
    1 ≤ pullCount I a t ω ∧ pullCount I a t ω ≤ t + 1 - K := by
  rw [pullCount_eq_init_add hrun a t hKt ω]
  have := (Finset.card_filter_le (Finset.Ico K t) (fun s => I (s + 1) ω = a)).trans
    (Nat.card_Ico K t).le
  omega

lemma pullCount_mono {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (a : Fin K) {t t' : ℕ}
    (h : t ≤ t') (ω : Ω) : pullCount I a t ω ≤ pullCount I a t' ω := by
  unfold pullCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

lemma pullCount_succ_of_eq {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (a : Fin K) (t : ℕ) (ω : Ω)
    (h : I (t + 1) ω = a) : pullCount I a (t + 1) ω = pullCount I a t ω + 1 := by
  unfold pullCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

lemma measurable_pullCount {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (a : Fin K) (t : ℕ) :
    Measurable (fun ω => pullCount I a t ω) := by
  have : (fun ω => pullCount I a t ω) =
      fun ω => ∑ s ∈ Finset.range t, if I (s + 1) ω = a then 1 else 0 := by
    funext ω; unfold pullCount; rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  exact Measurable.ite ((hI (s + 1)) (measurableSet_singleton a)) measurable_const measurable_const

lemma sum_measureReal_inter_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (C : ι → Set α) (hC : ∀ i, MeasurableSet (C i)) (S : Finset ι)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j)) (B : Set α) :
    ∑ i ∈ S, μ.real (B ∩ C i) ≤ μ.real B := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    have hd' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (C x) (C y) := fun x hx y hy hxy =>
      hd x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have h1 := ih hd' (B \ C i)
    have heq : ∀ j ∈ S, μ.real ((B \ C i) ∩ C j) = μ.real (B ∩ C j) := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hdis := hd i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj) hij
      congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨⟨hb, _⟩, hc⟩; exact ⟨hb, hc⟩
      · rintro ⟨hb, hc⟩; exact ⟨⟨hb, fun hci => Set.disjoint_left.mp hdis hci hc⟩, hc⟩
    rw [Finset.sum_congr rfl heq] at h1
    have h2 := measureReal_inter_add_sdiff (μ := μ) (s := B) (hC i)
    linarith

theorem lt8_aux {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a : Fin K) (μdag : ℝ) (T : ℕ) (hT : K ≤ T) :
    ∑ t ∈ Finset.Ico K T, P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} ≤
      ∑ n ∈ Finset.Icc 1 (T - K),
        P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} := by
  set B : ℕ → Set Ω := fun n => {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))}
    with hB
  set C : ℕ → ℕ → Set Ω := fun n t => {ω | pullCount I a t ω = n ∧ I (t + 1) ω = a} with hCdef
  have hCm : ∀ n t, MeasurableSet (C n t) := fun n t =>
    ((measurable_pullCount I hI a t) (measurableSet_singleton n)).inter
      ((hI (t + 1)) (measurableSet_singleton a))
  have hstep : ∀ t ∈ Finset.Ico K T,
      P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} ≤
        ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n ∩ C n t) := by
    intro t ht
    have hKt : K ≤ t := (Finset.mem_Ico.mp ht).1
    have htT : t < T := (Finset.mem_Ico.mp ht).2
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    intro ω hω
    obtain ⟨hlt, hIa⟩ := hω
    have hb := pullCount_bounds hrun a t hKt ω
    simp only [Set.mem_iUnion]
    refine ⟨pullCount I a t ω, Finset.mem_Icc.mpr ⟨hb.1, by omega⟩, ?_, rfl, hIa⟩
    show μdag < klIndex F (sampleMean X a (pullCount I a t ω) ω) (f₁ T / (pullCount I a t ω : ℝ))
    have hpos : (0 : ℝ) < pullCount I a t ω := by exact_mod_cast hb.1
    refine lt_of_lt_of_le hlt (klIndex_mono F hnat _ ?_)
    exact div_le_div_of_nonneg_right (f₁_mono htT.le) hpos.le
  have hdisj : ∀ n, ∀ i ∈ Finset.Ico K T, ∀ j ∈ Finset.Ico K T, i ≠ j →
      Disjoint (C n i) (C n j) := by
    intro n i _ j _ hij
    rw [Set.disjoint_left]
    rintro ω ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have := pullCount_mono I a (Nat.succ_le_of_lt h) ω
      rw [pullCount_succ_of_eq I a i ω hi2] at this
      omega
    · have := pullCount_mono I a (Nat.succ_le_of_lt h) ω
      rw [pullCount_succ_of_eq I a j ω hj2] at this
      omega
  calc ∑ t ∈ Finset.Ico K T, P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a}
      ≤ ∑ t ∈ Finset.Ico K T, ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n ∩ C n t) :=
        Finset.sum_le_sum hstep
    _ = ∑ n ∈ Finset.Icc 1 (T - K), ∑ t ∈ Finset.Ico K T, P.real (B n ∩ C n t) :=
        Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        exact sum_measureReal_inter_le P (C n) (hCm n) _ (hdisj n) (B n)


/-- Tangent-line bound from the left: `b φ ≥ b ψ + ḃ ψ (φ - ψ)` for `φ ≤ ψ` in `Θ`. -/
lemma expFam_tangent' (F : ExpFamily) {ψ φ : ℝ} (hψ : ψ ∈ F.Θ) (hφ : φ ∈ F.Θ) (h : φ ≤ ψ) :
    F.b ψ + deriv F.b ψ * (φ - ψ) ≤ F.b φ := by
  set D := F.Θ ∩ Set.Iic ψ with hD
  have hDc : Convex ℝ D := (expFam_convex F).inter (convex_Iic ψ)
  have hsub : D ⊆ F.Θ := Set.inter_subset_left
  have hcont : ContinuousOn (fun x => F.b x - deriv F.b ψ * x) D :=
    (F.contDiff.continuousOn.mono hsub).sub (continuousOn_const.mul continuousOn_id)
  have hint : ∀ x ∈ interior D, x ∈ D := fun x hx => interior_subset hx
  have hdiff : DifferentiableOn ℝ (fun x => F.b x - deriv F.b ψ * x) (interior D) := by
    intro x hx
    exact ((expFam_diffAt F (hsub (hint x hx))).sub
      ((differentiableAt_id).const_mul _)).differentiableWithinAt
  have hanti := antitoneOn_of_deriv_nonpos hDc hcont hdiff (by
    intro x hx
    have hxD := hint x hx
    have hd : deriv (fun x => F.b x - deriv F.b ψ * x) x = deriv F.b x - deriv F.b ψ := by
      have h : HasDerivAt (fun x => F.b x - deriv F.b ψ * x) (deriv F.b x - deriv F.b ψ * 1) x :=
        (expFam_diffAt F (hsub hxD)).hasDerivAt.sub ((hasDerivAt_id x).const_mul (deriv F.b ψ))
      rw [h.deriv, mul_one]
    rw [hd, sub_nonpos]
    exact (expFam_deriv_strictMono F).monotoneOn (hsub hxD) hψ hxD.2)
  have := hanti ⟨hφ, h⟩ ⟨hψ, Set.mem_Iic.mpr le_rfl⟩ h
  simp only at this
  nlinarith

lemma expFam_integrable_exp (F : ExpFamily) {ψ : ℝ} (hψ : ψ ∈ F.Θ) :
    Integrable (fun x => Real.exp (ψ * x)) F.ξ := by
  refine ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
    expFam_lintegral_exp F hψ]
  exact ENNReal.ofReal_lt_top

lemma expFam_mgf (F : ExpFamily) {ψ : ℝ} (hψ : ψ ∈ F.Θ) :
    mgf id F.ξ ψ = Real.exp (F.b ψ) := by
  unfold mgf
  simp only [id]
  have hm : AEStronglyMeasurable (fun x : ℝ => Real.exp (ψ * x)) F.ξ :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (ψ * x)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => Real.exp (ψ * x))
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hm,
    expFam_lintegral_exp F hψ, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- `ḃ(θ) = e^{-b θ} ∫ x e^{θ x} dξ`. -/
lemma expFam_deriv_b (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) :
    deriv F.b θ = Real.exp (- F.b θ) * ∫ x, x * Real.exp (θ * x) ∂F.ξ := by
  have hsub : F.Θ ⊆ integrableExpSet id F.ξ := fun ψ hψ => expFam_integrable_exp F hψ
  have hint : θ ∈ interior (integrableExpSet id F.ξ) :=
    interior_maximal hsub F.isOpen_Θ hθ
  have hm := hasDerivAt_mgf hint
  have hpos : mgf id F.ξ θ ≠ 0 := by rw [expFam_mgf F hθ]; exact (Real.exp_pos _).ne'
  have hlog := hm.log hpos
  have heq : F.b =ᶠ[nhds θ] fun ψ => Real.log (mgf id F.ξ ψ) := by
    filter_upwards [F.isOpen_Θ.mem_nhds hθ] with ψ hψ
    rw [expFam_mgf F hψ, Real.log_exp]
  rw [heq.deriv_eq, hlog.deriv, expFam_mgf F hθ, Real.exp_neg]
  simp only [id]
  field_simp
  congr 1
  funext x
  ring_nf

/-- The mean of `ν_θ` is `ḃ(θ)`. -/
lemma expFam_mean (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) :
    ∫ x, x ∂(F.arm θ) = deriv F.b θ := by
  unfold ExpFamily.arm
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - F.b θ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  rw [expFam_deriv_b F hθ, ← integral_const_mul]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, Real.exp_sub, Real.exp_neg]
  field_simp

lemma arm_mean_mem {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a)) (a : Fin K) :
    μ a = deriv F.b (θ a) := by
  rw [← hX.mean a, ← expFam_mean F (hθ a), ← hlaw a]
  exact (integral_map (hX.measurable a 0).aemeasurable aestronglyMeasurable_id).symm

lemma expFam_d_nonneg (F : ExpFamily) {m m' : ℝ} (hm : m ∈ F.M) (hm' : m' ∈ F.M) :
    0 ≤ F.d m m' := by
  have h1 : F.θof m ∈ F.Θ := Function.invFunOn_mem hm
  have h2 : deriv F.b (F.θof m) = m := Function.invFunOn_eq hm
  have h1' : F.θof m' ∈ F.Θ := Function.invFunOn_mem hm'
  unfold ExpFamily.d
  rcases le_total (F.θof m) (F.θof m') with h | h
  · have := expFam_tangent F h1 h1' h
    rw [h2] at this; linarith
  · have := expFam_tangent' F h1 h1' h
    rw [h2] at this; linarith

lemma f₁_pos (t : ℕ) : 0 < f₁ t := by
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have key : ∀ x : ℝ, 3 ≤ x → 0 < Real.log x + 3 * Real.log (Real.log x) := by
    intro x hx
    have hlx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
    linarith
  unfold f₁
  split_ifs with h
  · exact key 3 le_rfl
  · exact key t (le_of_lt (by exact_mod_cast (by omega : 3 < t)))


theorem gb10_aux {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a astar : Fin K) (hastar : μ astar = bestMean μ)
    (ha : μ a < bestMean μ) (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      f₁ T / F.d (μ a) (bestMean μ)
        + ∑ n ∈ Finset.Icc (⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ + 1) (T - K),
            P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))}
        + ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag}
        + 2 := by
  have hdpos : 0 ≤ F.d (μ a) (bestMean μ) := by
    apply expFam_d_nonneg
    · rw [arm_mean_mem F P X μ hX θ hθ hlaw a]; exact ⟨θ a, hθ a, rfl⟩
    · rw [← hastar, arm_mean_mem F P X μ hX θ hθ hlaw astar]; exact ⟨θ astar, hθ astar, rfl⟩
  have hx0 : 0 ≤ f₁ T / F.d (μ a) (bestMean μ) := div_nonneg (f₁_pos T).le hdpos
  have hceil : ((⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ : ℕ) : ℝ) < f₁ T / F.d (μ a) (bestMean μ) + 1 :=
    Nat.ceil_lt_add_one hx0
  have hE := eds_aux hK F hnat P X μ hX θ hθ hlaw I hI hrun a astar hastar μdag T
  have htail : 0 ≤ ∑ n ∈ Finset.Icc (⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ + 1) (T - K),
      P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hS1 : 0 ≤ ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag} :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  by_cases hKT : K ≤ T
  · have hL := lt8_aux hK F hnat P X μ hX θ hθ hlaw I hI hrun a μdag T hKT
    set n0 := ⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ with hn0
    have hsub : Finset.Icc 1 (T - K) ⊆ Finset.Icc 1 n0 ∪ Finset.Icc (n0 + 1) (T - K) := by
      intro n hn
      simp only [Finset.mem_Icc, Finset.mem_union] at hn ⊢
      omega
    have hdisj : Disjoint (Finset.Icc 1 n0) (Finset.Icc (n0 + 1) (T - K)) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    have hsplit : ∑ n ∈ Finset.Icc 1 (T - K),
          P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} ≤
        (n0 : ℝ) + ∑ n ∈ Finset.Icc (n0 + 1) (T - K),
          P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} := by
      calc ∑ n ∈ Finset.Icc 1 (T - K),
            P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))}
          ≤ ∑ n ∈ Finset.Icc 1 n0 ∪ Finset.Icc (n0 + 1) (T - K),
            P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => measureReal_nonneg)
        _ = ∑ n ∈ Finset.Icc 1 n0,
              P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} +
            ∑ n ∈ Finset.Icc (n0 + 1) (T - K),
              P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} :=
            Finset.sum_union hdisj
        _ ≤ (n0 : ℝ) + ∑ n ∈ Finset.Icc (n0 + 1) (T - K),
              P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} := by
            gcongr
            calc ∑ n ∈ Finset.Icc 1 n0,
                  P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))}
                ≤ ∑ n ∈ Finset.Icc 1 n0, (1 : ℝ) :=
                  Finset.sum_le_sum (fun _ _ => measureReal_le_one)
              _ = n0 := by simp
    linarith
  · have hempty : Finset.Ico K T = ∅ := Finset.Ico_eq_empty (by omega)
    have hempty2 : Finset.Icc (⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ + 1) (T - K) = ∅ :=
      Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, Finset.sum_empty] at hE
    rw [hempty, hempty2, Finset.sum_empty, Finset.sum_empty]
    linarith


/-- mgf of the arm law: `∫ e^{λx} dν_θ = e^{b(θ+λ) - b(θ)}` when `θ + λ ∈ Θ`. -/
lemma arm_lintegral_exp (F : ExpFamily) {θ l : ℝ} (hθ : θ ∈ F.Θ) (hθl : θ + l ∈ F.Θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (l * x)) ∂(F.arm θ) =
      ENNReal.ofReal (Real.exp (F.b (θ + l) - F.b θ)) := by
  unfold ExpFamily.arm
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - F.b θ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (l * x))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas hm2]
  have heq : ∀ x : ℝ, ((fun x => ENNReal.ofReal (Real.exp (θ * x - F.b θ))) *
      (fun x => ENNReal.ofReal (Real.exp (l * x)))) x =
      ENNReal.ofReal (Real.exp ((θ + l) * x)) * ENNReal.ofReal (Real.exp (- F.b θ)) := by
    intro x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  simp_rw [heq]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, expFam_lintegral_exp F hθl,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, sub_eq_add_neg]

lemma arm_mgf {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) (k : ℕ) {l : ℝ} (hl : θ a + l ∈ F.Θ) :
    Integrable (fun ω => Real.exp (l * X a k ω)) P ∧
      mgf (X a k) P l = Real.exp (F.b (θ a + l) - F.b (θ a)) := by
  have hid := (hX.identDistrib a k).comp (show Measurable (fun x : ℝ => Real.exp (l * x)) by fun_prop)
  have hm0 : Measurable (X a 0) := hX.measurable a 0
  have hlin : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X a 0 ω)) ∂P =
      ENNReal.ofReal (Real.exp (F.b (θ a + l) - F.b (θ a))) := by
    have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (l * x))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [← arm_lintegral_exp F (hθ a) hl, ← hlaw a, lintegral_map hm2 hm0]
  have hint0 : Integrable (fun ω => Real.exp (l * X a 0 ω)) P := by
    refine ⟨(by fun_prop : Measurable fun ω => Real.exp (l * X a 0 ω)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
      hlin]
    exact ENNReal.ofReal_lt_top
  have hintk : Integrable (fun ω => Real.exp (l * X a k ω)) P := hid.integrable_iff.mpr hint0
  refine ⟨hintk, ?_⟩
  have h1 : mgf (X a k) P l = mgf (X a 0) P l := by
    unfold mgf
    exact hid.integral_eq
  rw [h1]
  unfold mgf
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    hint0.aestronglyMeasurable, hlin, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- Chernoff bound for the sample mean of an exponential-family arm, upper tail:
`P(μ̂_n ≥ x) ≤ exp(-n (l x - (b(θ+l) - b(θ))))` for every `l ≥ 0` with `θ + l ∈ Θ`. -/
lemma chernoff_upper_l {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) (n : ℕ) (hn : 1 ≤ n) (x l : ℝ) (hl0 : 0 ≤ l) (hl : θ a + l ∈ F.Θ) :
    P.real {ω | x ≤ sampleMean X a n ω} ≤
      Real.exp (- (n : ℝ) * (l * x - (F.b (θ a + l) - F.b (θ a)))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hind : iIndepFun (fun k : ℕ => X a k) P :=
    hX.indep.precomp (g := fun k : ℕ => (a, k)) (fun i j h => by simpa using h)
  have hmeas : ∀ k, Measurable (X a k) := fun k => hX.measurable a k
  set S : Ω → ℝ := ∑ k ∈ Finset.range n, X a k with hS
  have hset : {ω | x ≤ sampleMean X a n ω} = {ω | (n : ℝ) * x ≤ S ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, sampleMean, hS, Finset.sum_apply]
    rw [le_div_iff₀ hnpos, mul_comm]
  have hintS : Integrable (fun ω => Real.exp (l * S ω)) P := by
    have := hind.integrable_exp_mul_sum (t := l) hmeas (s := Finset.range n)
      (fun k _ => (arm_mgf F P X μ hX θ hθ hlaw a k hl).1)
    simpa [hS] using this
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := S) ((n : ℝ) * x) hl0 hintS
  have hmgf : mgf S P l = Real.exp (F.b (θ a + l) - F.b (θ a)) ^ n := by
    rw [hS, hind.mgf_sum hmeas]
    rw [Finset.prod_congr rfl (fun k _ => (arm_mgf F P X μ hX θ hθ hlaw a k hl).2)]
    simp
  rw [hset]
  refine hch.trans (le_of_eq ?_)
  rw [hmgf, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring


/-! ## C2 analytic lemmas (session 2) -/

lemma θof_deriv (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) : F.θof (deriv F.b θ) = θ := by
  have hm : deriv F.b θ ∈ F.M := ⟨θ, hθ, rfl⟩
  exact (expFam_deriv_strictMono F).injOn (Function.invFunOn_mem hm) hθ (Function.invFunOn_eq hm)

lemma expFam_deriv2_contOn (F : ExpFamily) : ContinuousOn (deriv (deriv F.b)) F.Θ :=
  (F.contDiff.deriv_of_isOpen F.isOpen_Θ (by norm_num)).continuousOn_deriv_of_isOpen
    F.isOpen_Θ le_rfl

lemma expFam_deriv_diffAt (F : ExpFamily) {x : ℝ} (hx : x ∈ F.Θ) :
    DifferentiableAt ℝ (deriv F.b) x :=
  ((F.contDiff.deriv_of_isOpen (m := 1) F.isOpen_Θ (by norm_num)).differentiableOn one_ne_zero).differentiableAt
    (F.isOpen_Θ.mem_nhds hx)

/-- The variance of `ν_θ` is `b''(θ)`. -/
lemma var_arm (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) :
    variance id (F.arm θ) = deriv (deriv F.b) θ := by
  have hsub : F.Θ ⊆ integrableExpSet id F.ξ := fun ψ hψ => expFam_integrable_exp F hψ
  have hint : θ ∈ interior (integrableExpSet id F.ξ) := interior_maximal hsub F.isOpen_Θ hθ
  have hmgf : ∫ y, Real.exp (θ * y) ∂F.ξ = Real.exp (F.b θ) := expFam_mgf F hθ
  have harm : F.arm θ = F.ξ.tilted (fun x => θ * id x) := by
    unfold ExpFamily.arm Measure.tilted
    congr 1
    funext x
    simp only [id]
    rw [hmgf, ← Real.exp_sub]
  rw [harm, variance_tilted_mul hint, iteratedDeriv_succ, iteratedDeriv_one]
  have heq : cgf id F.ξ =ᶠ[nhds θ] F.b := by
    filter_upwards [F.isOpen_Θ.mem_nhds hθ] with ψ hψ
    unfold cgf; rw [expFam_mgf F hψ, Real.log_exp]
  exact heq.deriv.deriv_eq

/-- `b'' ≤ σ²` on `[θ₁, θ₂]`, with `σ² = varBound F (ḃθ₁) (ḃθ₂)`. -/
lemma deriv2_le_varBound (F : ExpFamily) {θ1 θ2 s : ℝ} (h1 : θ1 ∈ F.Θ) (h2 : θ2 ∈ F.Θ)
    (hs : s ∈ Set.Icc θ1 θ2) :
    deriv (deriv F.b) s ≤ varBound F (deriv F.b θ1) (deriv F.b θ2) := by
  have hIcc : Set.Icc θ1 θ2 ⊆ F.Θ := F.ordConnected_Θ.out h1 h2
  have hsΘ : s ∈ F.Θ := hIcc hs
  have hmono := expFam_deriv_strictMono F
  have hS : ∀ θ ∈ {θ ∈ F.Θ | deriv F.b θ1 ≤ deriv F.b θ ∧ deriv F.b θ ≤ deriv F.b θ2},
      θ ∈ Set.Icc θ1 θ2 := by
    intro θ ⟨hθ, ha, hb⟩
    exact ⟨(hmono.le_iff_le h1 hθ).mp ha, (hmono.le_iff_le hθ h2).mp hb⟩
  have hbdd : BddAbove ((fun θ => variance id (F.arm θ)) ''
      {θ ∈ F.Θ | deriv F.b θ1 ≤ deriv F.b θ ∧ deriv F.b θ ≤ deriv F.b θ2}) := by
    obtain ⟨B, hB⟩ := (isCompact_Icc.bddAbove_image ((expFam_deriv2_contOn F).mono hIcc) :
      BddAbove (deriv (deriv F.b) '' Set.Icc θ1 θ2))
    refine ⟨B, ?_⟩
    rintro _ ⟨θ, hθS, rfl⟩
    simp only
    rw [var_arm F hθS.1]
    exact hB ⟨θ, hS θ hθS, rfl⟩
  unfold varBound
  have hmem : s ∈ {θ ∈ F.Θ | deriv F.b θ1 ≤ deriv F.b θ ∧ deriv F.b θ ≤ deriv F.b θ2} :=
    ⟨hsΘ, hmono.monotoneOn h1 hsΘ hs.1, hmono.monotoneOn hsΘ h2 hs.2⟩
  have h' : variance id (F.arm s) ≤ _ := le_csSup hbdd ⟨s, hmem, rfl⟩
  rw [var_arm F hsΘ] at h'
  exact h'

/-- MVT: `ḃ y - ḃ x ≤ σ² (y - x)` for `θ₁ ≤ x ≤ y ≤ θ₂`. -/
lemma deriv_b_sub_le (F : ExpFamily) {θ1 θ2 x y : ℝ} (h1 : θ1 ∈ F.Θ) (h2 : θ2 ∈ F.Θ)
    (hx : x ∈ Set.Icc θ1 θ2) (hy : y ∈ Set.Icc θ1 θ2) (hxy : x ≤ y) :
    deriv F.b y - deriv F.b x ≤ varBound F (deriv F.b θ1) (deriv F.b θ2) * (y - x) := by
  have hIcc : Set.Icc θ1 θ2 ⊆ F.Θ := F.ordConnected_Θ.out h1 h2
  apply (convex_Icc θ1 θ2).image_sub_le_mul_sub_of_deriv_le
  · exact (F.contDiff.continuousOn_deriv_of_isOpen F.isOpen_Θ (by norm_num)).mono hIcc
  · intro z hz
    exact (expFam_deriv_diffAt F (hIcc (interior_subset hz))).differentiableWithinAt
  · intro z hz
    exact deriv2_le_varBound F h1 h2 (interior_subset hz)
  · exact hx
  · exact hy
  · exact hxy

/-- Sub-Gaussian cgf bound on `[θ₁, θ₂]`. -/
lemma b_taylor_le (F : ExpFamily) {θ1 θ2 l : ℝ} (h1 : θ1 ∈ F.Θ) (h2 : θ2 ∈ F.Θ) (hl0 : 0 ≤ l)
    (hl : θ1 + l ≤ θ2) :
    F.b (θ1 + l) - F.b θ1 - l * deriv F.b θ1 ≤
      varBound F (deriv F.b θ1) (deriv F.b θ2) * l ^ 2 / 2 := by
  set σ2 := varBound F (deriv F.b θ1) (deriv F.b θ2) with hσ2
  have hIcc : Set.Icc θ1 θ2 ⊆ F.Θ := F.ordConnected_Θ.out h1 h2
  set φ : ℝ → ℝ := fun s => σ2 * (s - θ1) ^ 2 / 2 - (F.b s - F.b θ1 - (s - θ1) * deriv F.b θ1)
    with hφ
  have hD : Set.Icc θ1 (θ1 + l) ⊆ Set.Icc θ1 θ2 := Set.Icc_subset_Icc le_rfl hl
  have hcont : ContinuousOn φ (Set.Icc θ1 (θ1 + l)) := by
    have hb : ContinuousOn F.b (Set.Icc θ1 (θ1 + l)) :=
      F.contDiff.continuousOn.mono (hD.trans hIcc)
    simp only [hφ]
    fun_prop
  have hderiv : ∀ s ∈ Set.Icc θ1 θ2, HasDerivAt φ (σ2 * (s - θ1) - (deriv F.b s - deriv F.b θ1)) s := by
    intro s hs
    have hb := (expFam_diffAt F (hIcc hs)).hasDerivAt
    have := (((hasDerivAt_id' s).sub_const θ1).pow 2).const_mul σ2 |>.div_const 2 |>.sub
      ((hb.sub_const (F.b θ1)).sub (((hasDerivAt_id' s).sub_const θ1).mul_const (deriv F.b θ1)))
    exact this.congr_deriv (by norm_num; ring)
  have hmono : MonotoneOn φ (Set.Icc θ1 (θ1 + l)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
    · intro s hs
      exact (hderiv s (hD (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hderiv s (hD hs')).deriv]
      have h12 : θ1 ≤ θ2 := by linarith
      have := deriv_b_sub_le F h1 h2 (Set.left_mem_Icc.mpr h12) (hD hs') hs'.1
      linarith
  have := hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
    (by linarith)
  have e0 : φ θ1 = 0 := by simp [hφ]
  have el : φ (θ1 + l) = σ2 * l ^ 2 / 2 - (F.b (θ1 + l) - F.b θ1 - l * deriv F.b θ1) := by
    simp only [hφ]; ring_nf
  rw [e0, el] at this
  linarith

/-- `∑_{j<N} e^{-a (j+1)^2} ≤ √(π/a)/2`. -/
lemma gauss_sum_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ Finset.range N, Real.exp (-a * ((j : ℝ) + 1) ^ 2) ≤ Real.sqrt (Real.pi / a) / 2 := by
  set f : ℝ → ℝ := fun x => Real.exp (-a * x ^ 2) with hf
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    simp only [hf]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ x := hx.1
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith
  have hsum := hanti.sum_le_integral
  have heq : ∑ j ∈ Finset.range N, Real.exp (-a * ((j : ℝ) + 1) ^ 2) =
      ∑ i ∈ Finset.range N, f (0 + ((i + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [hf]
  rw [heq]
  refine hsum.trans ?_
  rw [zero_add, intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq ha).integrableOn
  have hle : ∫ x in Set.Ioc (0 : ℝ) N, f x ≤ ∫ x in Set.Ioi (0 : ℝ), f x := by
    apply MeasureTheory.setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
    · exact Filter.Eventually.of_forall Set.Ioc_subset_Ioi_self
  refine hle.trans (le_of_eq ?_)
  simp only [hf]
  rw [integral_gaussian_Ioi]

/-- `∑_{j<N} e^{-b (j+1)} ≤ 1/b`. -/
lemma geom_exp_sum_le {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ∑ j ∈ Finset.range N, Real.exp (-b * ((j : ℝ) + 1)) ≤ 1 / b := by
  have key : ∀ N : ℕ, ∑ j ∈ Finset.range N, Real.exp (-b * ((j : ℝ) + 1)) ≤
      (1 - Real.exp (-b * N)) / b := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : Real.exp (-b * ((n : ℝ) + 1)) = Real.exp (-b * n) * Real.exp (-b) := by
        rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp (-b * ((n + 1 : ℕ) : ℝ)) = Real.exp (-b * n) * Real.exp (-b) := by
        push_cast; rw [← Real.exp_add]; ring_nf
      rw [h2]
      rw [h1]
      have he : Real.exp (-b) * (b + 1) ≤ 1 := by
        have := Real.add_one_le_exp b
        have hpos := Real.exp_pos (-b)
        calc Real.exp (-b) * (b + 1) ≤ Real.exp (-b) * Real.exp b := by gcongr
          _ = 1 := by rw [← Real.exp_add]; simp
      have hen := Real.exp_pos (-b * n)
      have : Real.exp (-b * ↑n) * Real.exp (-b) ≤
          (Real.exp (-b * ↑n) - Real.exp (-b * ↑n) * Real.exp (-b)) / b := by
        rw [le_div_iff₀ hb]; nlinarith
      calc _ ≤ (1 - Real.exp (-b * ↑n)) / b + Real.exp (-b * ↑n) * Real.exp (-b) := by linarith
        _ ≤ (1 - Real.exp (-b * ↑n)) / b +
            (Real.exp (-b * ↑n) - Real.exp (-b * ↑n) * Real.exp (-b)) / b := by linarith
        _ = _ := by ring
  refine (key N).trans ?_
  apply div_le_div_of_nonneg_right _ hb.le
  linarith [Real.exp_pos (-b * N)]

/-- Pointwise split of the self-normalised Gaussian term. -/
lemma tail_term_le {d c f n : ℝ} (hd : 0 < d) (hc : 0 < c) (hf : 0 < f) (hn : f / d < n) :
    Real.exp (-((n * d - f) ^ 2 / (2 * c * n))) ≤
      Real.exp (-(d ^ 3 / (4 * c * f)) * (n - f / d) ^ 2) + Real.exp (-(d ^ 2 / (8 * c)) * n) := by
  have hnpos : 0 < n := lt_trans (div_pos hf hd) hn
  have hnd : f < n * d := by rwa [div_lt_iff₀ hd] at hn
  rcases le_or_gt n (2 * f / d) with h | h
  · have hle : Real.exp (-((n * d - f) ^ 2 / (2 * c * n))) ≤
        Real.exp (-(d ^ 3 / (4 * c * f)) * (n - f / d) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hn2 : n * d ≤ 2 * f := by rwa [le_div_iff₀ hd] at h
      have e1 : (n - f / d) ^ 2 = (n * d - f) ^ 2 / d ^ 2 := by
        field_simp
      rw [e1]
      have hA : 0 ≤ (n * d - f) ^ 2 := sq_nonneg _
      rw [neg_mul, neg_le_neg_iff]
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have : d ^ 3 * (2 * c * n) ≤ 4 * c * f * d ^ 2 := by
        have : d ^ 3 * (2 * c * n) = 2 * c * d ^ 2 * (n * d) := by ring
        rw [this]
        have : 4 * c * f * d ^ 2 = 2 * c * d ^ 2 * (2 * f) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_left hn2; positivity
      calc d ^ 3 * (n * d - f) ^ 2 * (2 * c * n) = (d ^ 3 * (2 * c * n)) * (n * d - f) ^ 2 := by ring
        _ ≤ (4 * c * f * d ^ 2) * (n * d - f) ^ 2 := by gcongr
        _ = (n * d - f) ^ 2 * (4 * c * f * d ^ 2) := by ring
    linarith [Real.exp_pos (-(d ^ 2 / (8 * c)) * n)]
  · have hle : Real.exp (-((n * d - f) ^ 2 / (2 * c * n))) ≤ Real.exp (-(d ^ 2 / (8 * c)) * n) := by
      apply Real.exp_le_exp.mpr
      have hn2 : 2 * f < n * d := by rwa [div_lt_iff₀ hd] at h
      have h3 : n * d / 2 ≤ n * d - f := by linarith
      have h4 : (n * d / 2) ^ 2 ≤ (n * d - f) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h3
      rw [neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      calc d ^ 2 / (8 * c) * n * (2 * c * n) = (n * d / 2) ^ 2 := by field_simp; ring
        _ ≤ _ := h4
    linarith [Real.exp_pos (-(d ^ 3 / (4 * c * f)) * (n - f / d) ^ 2)]

/-- The full deterministic sum of C2. -/
lemma tail_sum_le {d c f : ℝ} (hd : 0 < d) (hc : 0 < c) (hf : 0 < f) (N : ℕ) :
    ∑ n ∈ Finset.Icc (⌈f / d⌉₊ + 1) N, Real.exp (-(((n : ℝ) * d - f) ^ 2 / (2 * c * n))) ≤
      Real.sqrt (Real.pi * c * f / d ^ 3) + 8 * c / d ^ 2 := by
  set n0 := ⌈f / d⌉₊ + 1 with hn0
  set a := d ^ 3 / (4 * c * f) with ha
  set b := d ^ 2 / (8 * c) with hb
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hceil : f / d ≤ (⌈f / d⌉₊ : ℝ) := Nat.le_ceil _
  have hpt : ∀ n ∈ Finset.Icc n0 N, Real.exp (-(((n : ℝ) * d - f) ^ 2 / (2 * c * n))) ≤
      Real.exp (-a * (((n - n0 : ℕ) : ℝ) + 1) ^ 2) + Real.exp (-b * (((n - 1 : ℕ) : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (n0 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hlt : f / d < n := by
      have : ((⌈f / d⌉₊ + 1 : ℕ) : ℝ) = (⌈f / d⌉₊ : ℝ) + 1 := by push_cast; ring
      rw [hn0] at hn1; rw [this] at hn1; linarith
    refine (tail_term_le hd hc hf hlt).trans (add_le_add ?_ (le_of_eq ?_))
    · apply Real.exp_le_exp.mpr
      have hcast : (((n - n0 : ℕ) : ℝ) + 1) = (n : ℝ) - n0 + 1 := by
        rw [Nat.cast_sub hn.1]
      rw [hcast]
      have h0 : 0 ≤ (n : ℝ) - n0 + 1 := by linarith
      have h1 : (n : ℝ) - n0 + 1 ≤ n - f / d := by
        have : ((n0 : ℕ) : ℝ) = (⌈f / d⌉₊ : ℝ) + 1 := by rw [hn0]; push_cast; ring
        rw [this]; linarith
      have : ((n : ℝ) - n0 + 1) ^ 2 ≤ (n - f / d) ^ 2 := pow_le_pow_left₀ h0 h1 2
      rw [← ha]
      nlinarith
    · have h1 : 1 ≤ n := by omega
      rw [← hb, Nat.cast_sub h1]; push_cast; ring_nf
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · -- reindex Icc n0 N as n0 + j, j < N + 1 - n0
    have hre : ∑ n ∈ Finset.Icc n0 N, Real.exp (-a * (((n - n0 : ℕ) : ℝ) + 1) ^ 2) =
        ∑ j ∈ Finset.range (N + 1 - n0), Real.exp (-a * ((j : ℝ) + 1) ^ 2) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp
    rw [hre]
    refine (gauss_sum_le hapos _).trans (le_of_eq ?_)
    rw [ha]
    have : Real.pi / (d ^ 3 / (4 * c * f)) = 4 * (Real.pi * c * f / d ^ 3) := by
      field_simp
    rw [this, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    ring
  · have hsub : Finset.Icc n0 N ⊆ Finset.Icc 1 N := by
      intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    have hnn : ∀ n ∈ Finset.Icc 1 N, 0 ≤ Real.exp (-b * (((n - 1 : ℕ) : ℝ) + 1)) :=
      fun n _ => (Real.exp_pos _).le
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n h _ => hnn n h)).trans ?_
    have hre : ∑ n ∈ Finset.Icc 1 N, Real.exp (-b * (((n - 1 : ℕ) : ℝ) + 1)) =
        ∑ j ∈ Finset.range N, Real.exp (-b * ((j : ℝ) + 1)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr (by simp)
      intro j _
      simp [add_comm]
    rw [hre]
    refine (geom_exp_sum_le hbpos N).trans (le_of_eq ?_)
    rw [hb]; field_simp


/-- Sub-Gaussian Chernoff bound on `[μa, ḃθ₂]`. -/
lemma chernoff_subgauss {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) {θ2 : ℝ} (h2 : θ2 ∈ F.Θ) (h12 : θ a ≤ θ2)
    (hσ : 0 < varBound F (deriv F.b (θ a)) (deriv F.b θ2))
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx1 : deriv F.b (θ a) ≤ x) (hx2 : x ≤ deriv F.b θ2) :
    P.real {ω | x ≤ sampleMean X a n ω} ≤
      Real.exp (- (n : ℝ) * (x - deriv F.b (θ a)) ^ 2 /
        (2 * varBound F (deriv F.b (θ a)) (deriv F.b θ2))) := by
  set σ2 := varBound F (deriv F.b (θ a)) (deriv F.b θ2) with hσ2
  set l := (x - deriv F.b (θ a)) / σ2 with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hσ.le
  have hm := deriv_b_sub_le F (hθ a) h2 (Set.left_mem_Icc.mpr h12) (Set.right_mem_Icc.mpr h12) h12
  have hlD : θ a + l ≤ θ2 := by
    have : l ≤ θ2 - θ a := by
      rw [hl, div_le_iff₀ hσ]; nlinarith
    linarith
  have hlΘ : θ a + l ∈ F.Θ := F.ordConnected_Θ.out (hθ a) h2 ⟨by linarith, hlD⟩
  have hch := chernoff_upper_l F P X μ hX θ hθ hlaw a n hn x l hl0 hlΘ
  have ht := b_taylor_le F (hθ a) h2 hl0 hlD
  refine hch.trans (Real.exp_le_exp.mpr ?_)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hlσ : l * σ2 = x - deriv F.b (θ a) := by rw [hl]; field_simp
  have h3 : l * (x - deriv F.b (θ a)) = σ2 * l ^ 2 := by rw [← hlσ]; ring
  have e : (x - deriv F.b (θ a)) ^ 2 / (2 * σ2) = σ2 * l ^ 2 / 2 := by
    rw [← hlσ]; field_simp
  have key : (x - deriv F.b (θ a)) ^ 2 / (2 * σ2) ≤ l * x - (F.b (θ a + l) - F.b (θ a)) := by
    rw [e]; nlinarith
  have := mul_le_mul_of_nonneg_left key hn0
  have e2 : -(n : ℝ) * (x - deriv F.b (θ a)) ^ 2 / (2 * σ2) =
      -((n : ℝ) * ((x - deriv F.b (θ a)) ^ 2 / (2 * σ2))) := by ring
  rw [e2]
  linarith

/-- The kl-UCB index exceeds `ḃθ₂` only if the empirical mean is above the tangent threshold. -/
lemma klIndex_event_sub (F : ExpFamily) {θ1 θ2 : ℝ} (h1 : θ1 ∈ F.Θ)
    (h2 : θ2 ∈ F.Θ) (h12 : θ1 < θ2) {m γ : ℝ} (hγ : 0 ≤ γ)
    (h : deriv F.b θ2 < klIndex F m γ) :
    deriv F.b θ1 + (F.b θ2 - F.b θ1 - deriv F.b θ1 * (θ2 - θ1) - γ) / (θ2 - θ1) ≤ m := by
  have hD : 0 < θ2 - θ1 := by linarith
  have htan' := expFam_tangent' F h2 h1 h12.le
  by_contra hm
  push Not at hm
  have hm2 : m ≤ deriv F.b θ2 := by
    have : (F.b θ2 - F.b θ1 - deriv F.b θ1 * (θ2 - θ1) - γ) / (θ2 - θ1) ≤
        deriv F.b θ2 - deriv F.b θ1 := by
      rw [div_le_iff₀ hD]; nlinarith
    linarith
  apply absurd h
  push Not
  apply csSup_le ⟨m, Or.inr rfl⟩
  rintro y (⟨hyM, hy⟩ | hy)
  · by_contra hlt
    push Not at hlt
    have hs : F.θof y ∈ F.Θ := Function.invFunOn_mem hyM
    have hsy : deriv F.b (F.θof y) = y := Function.invFunOn_eq hyM
    have hs2 : θ2 ≤ F.θof y := by
      by_contra hc; push Not at hc
      have := (expFam_deriv_strictMono F) hs h2 hc
      linarith
    have hterm : ENNReal.ofReal ((θ1 - F.θof y) * m - F.b θ1 + F.b (F.θof y)) ≤
        ENNReal.ofReal γ := by
      refine le_trans ?_ hy
      unfold dExt
      exact le_iSup (fun θ : F.Θ => ENNReal.ofReal (((θ : ℝ) - F.θof y) * m - F.b θ +
        F.b (F.θof y))) ⟨θ1, h1⟩
    rw [ENNReal.ofReal_le_ofReal_iff hγ] at hterm
    have htan := expFam_tangent F h2 hs hs2
    have hx : 0 ≤ (deriv F.b θ2 - m) * (F.θof y - θ2) := mul_nonneg (by linarith) (by linarith)
    have hkey : F.b θ2 - F.b θ1 - deriv F.b θ1 * (θ2 - θ1) - γ ≤ (m - deriv F.b θ1) * (θ2 - θ1) := by
      nlinarith
    have : (F.b θ2 - F.b θ1 - deriv F.b θ1 * (θ2 - θ1) - γ) / (θ2 - θ1) ≤ m - deriv F.b θ1 := by
      rw [div_le_iff₀ hD]; linarith
    linarith
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hm2

/-- The mean space is a neighbourhood of each of its points. -/
lemma M_mem_nhds (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) : F.M ∈ nhds (deriv F.b θ) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp F.isOpen_Θ θ hθ
  have hsub : Set.Icc (θ - δ / 2) (θ + δ / 2) ⊆ F.Θ := by
    intro x hx; apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hcont : ContinuousOn (deriv F.b) (Set.Icc (θ - δ / 2) (θ + δ / 2)) :=
    (F.contDiff.continuousOn_deriv_of_isOpen F.isOpen_Θ (by norm_num)).mono hsub
  have hIVT := intermediate_value_Icc (by linarith : θ - δ / 2 ≤ θ + δ / 2) hcont
  have hlo : deriv F.b (θ - δ / 2) < deriv F.b θ :=
    expFam_deriv_strictMono F (hsub ⟨le_rfl, by linarith⟩) hθ (by linarith)
  have hhi : deriv F.b θ < deriv F.b (θ + δ / 2) :=
    expFam_deriv_strictMono F hθ (hsub ⟨by linarith, le_rfl⟩) (by linarith)
  apply Filter.mem_of_superset (Icc_mem_nhds hlo hhi)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hIVT hy
  exact ⟨x, hsub hx, rfl⟩

lemma θof_hasDerivAt (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) :
    HasDerivAt F.θof (deriv (deriv F.b) θ)⁻¹ (deriv F.b θ) := by
  have hM := M_mem_nhds F hθ
  have hmono : MonotoneOn F.θof F.M := by
    intro y1 hy1 y2 hy2 hle
    by_contra hc; push Not at hc
    have := expFam_deriv_strictMono F (Function.invFunOn_mem hy2) (Function.invFunOn_mem hy1) hc
    rw [Function.invFunOn_eq hy1, Function.invFunOn_eq hy2] at this
    linarith
  have himg : F.θof '' F.M = F.Θ := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact Function.invFunOn_mem hy
    · intro hx; exact ⟨deriv F.b x, ⟨x, hx, rfl⟩, θof_deriv F hx⟩
  have hcont : ContinuousAt F.θof (deriv F.b θ) := by
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hmono hM
    rw [himg, θof_deriv F hθ]; exact F.isOpen_Θ.mem_nhds hθ
  have hf : HasDerivAt (deriv F.b) (deriv (deriv F.b) θ) (F.θof (deriv F.b θ)) := by
    rw [θof_deriv F hθ]; exact (expFam_deriv_diffAt F hθ).hasDerivAt
  apply HasDerivAt.of_local_left_inverse hcont hf (F.deriv2_pos θ hθ).ne'
  filter_upwards [hM] with y hy
  exact Function.invFunOn_eq hy

/-- `∂₁ d(m, μ')` at `m = ḃθ₁` equals `θ₁ - θof μ'`. -/
lemma deriv_d_first (F : ExpFamily) {θ1 : ℝ} (h1 : θ1 ∈ F.Θ) (μ' : ℝ) :
    deriv (fun m => F.d m μ') (deriv F.b θ1) = θ1 - F.θof μ' := by
  have hg := θof_hasDerivAt F h1
  have hb : HasDerivAt F.b (deriv F.b θ1) (F.θof (deriv F.b θ1)) := by
    rw [θof_deriv F h1]; exact (expFam_diffAt F h1).hasDerivAt
  have hcomp := hb.comp (deriv F.b θ1) hg
  have hall := ((hasDerivAt_const (deriv F.b θ1) (F.b (F.θof μ'))).sub hcomp).sub
    ((hasDerivAt_id' (deriv F.b θ1)).mul ((hasDerivAt_const (deriv F.b θ1) (F.θof μ')).sub hg))
  have hfun : (fun m => F.d m μ') =
      fun m => F.b (F.θof μ') - (F.b ∘ F.θof) m - m * (F.θof μ' - F.θof m) := rfl
  have h' : HasDerivAt (fun m => F.d m μ') (0 - deriv F.b θ1 * (deriv (deriv F.b) θ1)⁻¹ -
      (1 * (F.θof μ' - F.θof (deriv F.b θ1)) + deriv F.b θ1 * (0 - (deriv (deriv F.b) θ1)⁻¹)))
      (deriv F.b θ1) := hall
  rw [h'.deriv, θof_deriv F h1]
  ring

lemma b_gap_pos (F : ExpFamily) {θ1 θ2 : ℝ} (h1 : θ1 ∈ F.Θ) (h2 : θ2 ∈ F.Θ) (h12 : θ1 < θ2) :
    0 < F.b θ2 - F.b θ1 - deriv F.b θ1 * (θ2 - θ1) := by
  have hIcc : Set.Icc θ1 θ2 ⊆ F.Θ := F.ordConnected_Θ.out h1 h2
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope F.b h12 (F.contDiff.continuousOn.mono hIcc)
    (fun x hx => (expFam_diffAt F (hIcc (Set.Ioo_subset_Icc_self hx))).differentiableWithinAt)
  have hlt := expFam_deriv_strictMono F h1 (hIcc (Set.Ioo_subset_Icc_self hc)) hc.1
  rw [hcd, lt_div_iff₀ (by linarith)] at hlt
  linarith

/-- NEW child C2 (the exponential-family tail sum, proof of Theorem 1 pp. 14-16). -/
theorem suboptimal_tail_sum {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) (ha : μ a < bestMean μ) (T : ℕ) (hT : 3 ≤ T) :
    ∑ n ∈ Finset.Icc (⌈f₁ T / F.d (μ a) (bestMean μ)⌉₊ + 1) (T - K),
        P.real {ω | bestMean μ < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} ≤
      2 * Real.sqrt (2 * Real.pi * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a)) ^ 2
            / (F.d (μ a) (bestMean μ)) ^ 3)
          * Real.sqrt (Real.log T + 3 * Real.log (Real.log T))
        + 8 * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a) / F.d (μ a) (bestMean μ)) ^ 2
        + 1 := by
  have hne : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨astar, hastar⟩ := exists_eq_ciSup_of_finite (f := μ)
  have hbest : bestMean μ = deriv F.b (θ astar) := by
    rw [← arm_mean_mem F P X μ hX θ hθ hlaw astar, hastar]; rfl
  have hμa : μ a = deriv F.b (θ a) := arm_mean_mem F P X μ hX θ hθ hlaw a
  have h1 := hθ a
  have h2 := hθ astar
  have h12 : θ a < θ astar := by
    by_contra hc; push Not at hc
    have := (expFam_deriv_strictMono F).monotoneOn h2 h1 hc
    rw [← hμa, ← hbest] at this; linarith
  have hDpos : 0 < θ astar - θ a := by linarith
  have hdd : F.d (μ a) (bestMean μ) =
      F.b (θ astar) - F.b (θ a) - deriv F.b (θ a) * (θ astar - θ a) := by
    unfold ExpFamily.d; rw [hbest, hμa, θof_deriv F h1, θof_deriv F h2]
  have hddpos : 0 < F.d (μ a) (bestMean μ) := by rw [hdd]; exact b_gap_pos F h1 h2 h12
  have hderiv : deriv (fun m => F.d m (bestMean μ)) (μ a) = θ a - θ astar := by
    rw [hμa, deriv_d_first F h1, hbest, θof_deriv F h2]
  have hσ2' : varBound F (μ a) (bestMean μ) = varBound F (deriv F.b (θ a)) (deriv F.b (θ astar)) := by
    rw [hμa, hbest]
  have hσpos : 0 < varBound F (μ a) (bestMean μ) := by
    rw [hσ2']
    exact lt_of_lt_of_le (F.deriv2_pos (θ a) h1) (deriv2_le_varBound F h1 h2 ⟨le_rfl, h12.le⟩)
  rw [hderiv]
  set dd := F.d (μ a) (bestMean μ) with hdddef
  set σ2 := varBound F (μ a) (bestMean μ) with hσdef
  set D := θ astar - θ a with hD
  set f := f₁ T with hfdef
  have hfpos : 0 < f := f₁_pos T
  set c := σ2 * D ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hpt : ∀ n ∈ Finset.Icc (⌈f / dd⌉₊ + 1) (T - K),
      P.real {ω | bestMean μ < klIndex F (sampleMean X a n ω) (f / (n : ℝ))} ≤
        Real.exp (-(((n : ℝ) * dd - f) ^ 2 / (2 * c * n))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hfn : f / dd < n := by
      have := Nat.le_ceil (f / dd)
      have h' : ((⌈f / dd⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
      push_cast at h'; linarith
    have hγ : 0 ≤ f / (n:ℝ) := by positivity
    have hdfn : 0 < dd - f / n := by
      have h3 : f < n * dd := by rwa [div_lt_iff₀ hddpos] at hfn
      have : f / n < dd := by rw [div_lt_iff₀ hnpos]; linarith
      linarith
    have hsub : {ω | bestMean μ < klIndex F (sampleMean X a n ω) (f / (n : ℝ))} ⊆
        {ω | deriv F.b (θ a) + (dd - f / n) / D ≤ sampleMean X a n ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hbest] at hω
      have := klIndex_event_sub F h1 h2 h12 hγ hω
      rw [hdd]; exact this
    have hx1 : deriv F.b (θ a) ≤ deriv F.b (θ a) + (dd - f / n) / D := by
      have := div_pos hdfn hDpos; linarith
    have hx2 : deriv F.b (θ a) + (dd - f / n) / D ≤ deriv F.b (θ astar) := by
      have htan := expFam_tangent' F h2 h1 h12.le
      have : (dd - f / n) / D ≤ deriv F.b (θ astar) - deriv F.b (θ a) := by
        rw [div_le_iff₀ hDpos, hdd, hD]; nlinarith [hγ]
      linarith
    have hsg := chernoff_subgauss F P X μ hX θ hθ hlaw a h2 h12.le (by rw [← hσ2']; exact hσpos)
      n hn1 _ hx1 hx2
    refine (measureReal_mono hsub).trans (hsg.trans (le_of_eq ?_))
    rw [← hσ2']
    congr 1
    have hDne : D ≠ 0 := hDpos.ne'
    have hσne : σ2 ≠ 0 := hσpos.ne'
    have hnne : (n:ℝ) ≠ 0 := hnpos.ne'
    rw [hc]
    field_simp
    ring
  refine (Finset.sum_le_sum hpt).trans ?_
  have hsum := tail_sum_le hddpos hcpos hfpos (T - K)
  refine hsum.trans ?_
  have hf3 : f = Real.log T + 3 * Real.log (Real.log T) := by
    rw [hfdef]; unfold f₁
    split_ifs with h
    · have : T = 3 := by omega
      subst this; norm_num
    · rfl
  rw [← hf3]
  have hsq : (θ a - θ astar) ^ 2 = D ^ 2 := by rw [hD]; ring
  have e2 : 8 * c / dd ^ 2 = 8 * σ2 * ((θ a - θ astar) / dd) ^ 2 := by
    rw [div_pow, hsq, hc]; field_simp
  have hA : 0 ≤ Real.pi * c / dd ^ 3 := by positivity
  have e3 : 2 * Real.pi * σ2 * (θ a - θ astar) ^ 2 / dd ^ 3 = 2 * (Real.pi * c / dd ^ 3) := by
    rw [hsq, hc]; ring
  have e4 : Real.sqrt (Real.pi * c * f / dd ^ 3) =
      Real.sqrt (Real.pi * c / dd ^ 3) * Real.sqrt f := by
    rw [show Real.pi * c * f / dd ^ 3 = (Real.pi * c / dd ^ 3) * f by ring, Real.sqrt_mul hA]
  rw [e3, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), e4, e2]
  have hs2 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hAB : 0 ≤ Real.sqrt (Real.pi * c / dd ^ 3) * Real.sqrt f :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 2 * Real.sqrt 2 by linarith) hAB]


/-! ## C1 (session 2) -/

lemma f₁_gt_one (t : ℕ) : 1 < f₁ t := by
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have h0 : f₁ 0 = Real.log 3 + 3 * Real.log (Real.log 3) := by unfold f₁; simp
  have hll : 0 < Real.log (Real.log 3) := Real.log_pos h3
  have := f₁_mono (Nat.zero_le t)
  linarith

lemma dExt_self (F : ExpFamily) {θ0 : ℝ} (h0 : θ0 ∈ F.Θ) :
    dExt F (deriv F.b θ0) (deriv F.b θ0) = 0 := by
  unfold dExt
  rw [θof_deriv F h0]
  refine le_antisymm (iSup_le fun ⟨θ, hθ⟩ => ?_) zero_le
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
  rcases le_total θ0 θ with h | h
  · have := expFam_tangent F h0 hθ h
    simp only; nlinarith
  · have := expFam_tangent' F h0 hθ h
    simp only; nlinarith

/-- If `d(m, μ⋆) < γ` then the kl-UCB index `klIndex m γ` exceeds `μ⋆`. -/
lemma klIndex_gt (F : ExpFamily) (hnat : IsNatural F) {θ2 : ℝ} (h2 : θ2 ∈ F.Θ) {m γ : ℝ}
    (h : dExt F m (deriv F.b θ2) < ENNReal.ofReal γ) : deriv F.b θ2 < klIndex F m γ := by
  have hfin : dExt F m (deriv F.b θ2) ≠ ⊤ := ne_top_of_lt h
  set D0 := (dExt F m (deriv F.b θ2)).toReal with hD0
  have hD0e : dExt F m (deriv F.b θ2) = ENNReal.ofReal D0 := (ENNReal.ofReal_toReal hfin).symm
  have hD0nn : 0 ≤ D0 := ENNReal.toReal_nonneg
  have hlt : D0 < γ := by
    rw [hD0e] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hD0nn).mp h
  have hterm : ∀ θ ∈ F.Θ, (θ - θ2) * m - F.b θ + F.b θ2 ≤ D0 := by
    intro θ hθ
    have : ENNReal.ofReal ((θ - θ2) * m - F.b θ + F.b θ2) ≤ ENNReal.ofReal D0 := by
      rw [← hD0e]
      unfold dExt
      rw [θof_deriv F h2]
      exact le_iSup (fun θ' : F.Θ => ENNReal.ofReal (((θ' : ℝ) - θ2) * m - F.b θ' + F.b θ2)) ⟨θ, hθ⟩
    exact (ENNReal.ofReal_le_ofReal_iff hD0nn).mp this
  have hcont : ContinuousAt (fun s : ℝ => -s * m + F.b (θ2 + s) - F.b θ2) 0 := by
    have hb : ContinuousAt F.b (θ2 + 0) := by
      rw [add_zero]; exact (expFam_diffAt F h2).continuousAt
    exact ((continuousAt_id.neg.mul continuousAt_const).add
      (hb.comp (continuousAt_const.add continuousAt_id))).sub continuousAt_const
  have hval : (fun s : ℝ => -s * m + F.b (θ2 + s) - F.b θ2) 0 = 0 := by simp
  have hev1 := hcont.eventually (gt_mem_nhds
    (show (fun s : ℝ => -s * m + F.b (θ2 + s) - F.b θ2) 0 < γ - D0 by rw [hval]; linarith))
  have hev2 : ∀ᶠ s in nhds (0:ℝ), θ2 + s ∈ F.Θ := by
    have hc : ContinuousAt (fun s : ℝ => θ2 + s) 0 := continuousAt_const.add continuousAt_id
    exact hc.preimage_mem_nhds (by simp only [add_zero]; exact F.isOpen_Θ.mem_nhds h2)
  have hev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ((fun s : ℝ => -s * m + F.b (θ2 + s) - F.b θ2) s < γ - D0 ∧ θ2 + s ∈ F.Θ) ∧ s ∈ Set.Ioi 0 :=
    ((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := hev.exists
  simp only at hs1
  rw [Set.mem_Ioi] at hs0
  have hμ' : deriv F.b θ2 < deriv F.b (θ2 + s) :=
    expFam_deriv_strictMono F h2 hs2 (by linarith)
  have hdle : dExt F m (deriv F.b (θ2 + s)) ≤ ENNReal.ofReal γ := by
    unfold dExt
    rw [θof_deriv F hs2]
    refine iSup_le fun ⟨θ, hθ⟩ => ENNReal.ofReal_le_ofReal ?_
    have := hterm θ hθ
    simp only
    linarith
  have hmem : deriv F.b (θ2 + s) ∈ ({μ ∈ F.M | dExt F m μ ≤ ENNReal.ofReal γ} ∪ {m}) :=
    Or.inl ⟨⟨θ2 + s, hs2, rfl⟩, hdle⟩
  exact lt_of_lt_of_le hμ' (le_csSup (klIndex_bdd F hnat m γ) hmem)

/-- `log 3 ∈ (1.09, 1.1)`. -/
lemma log_three_bounds : (1.09 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.1 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h1 : 1 - 0.09 ≤ Real.exp (-0.09) := by linarith [Real.add_one_le_exp (-0.09 : ℝ)]
    have h2 : Real.exp 0.09 * Real.exp (-0.09) = 1 := by rw [← Real.exp_add]; norm_num
    have he := Real.exp_one_lt_d9
    have h3 : Real.exp 1.09 = Real.exp 1 * Real.exp 0.09 := by rw [← Real.exp_add]; norm_num
    have hp : 0 < Real.exp 0.09 := Real.exp_pos _
    have h4 : Real.exp 0.09 * 0.91 ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hp.le; linarith
    have h5 : Real.exp 0.09 ≤ 1 / 0.91 := by rw [le_div_iff₀ (by norm_num)]; linarith
    rw [h3]
    have h6 : Real.exp 1 * Real.exp 0.09 ≤ 2.7182818286 * (1 / 0.91) := by
      apply mul_le_mul he.le h5 hp.le (by norm_num)
    linarith
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.1 by norm_num)
    have he := Real.exp_one_gt_d9
    have h3 : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
    rw [h3]
    have h6 : 2.7182818283 * (1 + 0.1 + 0.1 ^ 2 / 2) ≤ Real.exp 1 * Real.exp 0.1 :=
      mul_le_mul he.le h1 (by norm_num) (Real.exp_pos _).le
    linarith

/-- The summand of (13) at `ε = f(t)`. -/
noncomputable def c1term (t : ℕ) : ℝ :=
  Real.exp 1 * (⌈f₁ t * Real.log t⌉₊ : ℝ) * Real.exp (-(f₁ t))

lemma c1term_nonneg (t : ℕ) : 0 ≤ c1term t := by
  unfold c1term; positivity

/-- `1/(t log t) ≤ log log t - log log (t-1)` for `t ≥ 4`. -/
lemma loglog_step (t : ℝ) (ht : 4 ≤ t) :
    1 / (t * Real.log t) ≤ Real.log (Real.log t) - Real.log (Real.log (t - 1)) := by
  have ht1 : 0 < t - 1 := by linarith
  have hL' : 0 < Real.log (t - 1) := Real.log_pos (by linarith)
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hstep1 : 1 / t ≤ Real.log t - Real.log (t - 1) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < t / (t - 1) by positivity)
    rw [Real.log_div (by positivity) ht1.ne', inv_div] at this
    have e : 1 - (t - 1) / t = 1 / t := by field_simp; ring
    linarith
  have hstep2 : (Real.log t - Real.log (t - 1)) / Real.log t ≤
      Real.log (Real.log t) - Real.log (Real.log (t - 1)) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < Real.log t / Real.log (t - 1) by positivity)
    rw [Real.log_div hL.ne' hL'.ne', inv_div] at this
    have e : 1 - Real.log (t - 1) / Real.log t = (Real.log t - Real.log (t - 1)) / Real.log t := by
      field_simp
    linarith
  have : 1 / (t * Real.log t) ≤ (Real.log t - Real.log (t - 1)) / Real.log t := by
    rw [show 1 / (t * Real.log t) = (1 / t) / Real.log t by field_simp]
    exact div_le_div_of_nonneg_right hstep1 hL.le
  linarith

lemma c1term_le (t : ℕ) (ht : 4 ≤ t) :
    c1term t ≤ 4 * Real.exp 1 * (Real.log (Real.log t) - Real.log (Real.log ((t : ℝ) - 1))) := by
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  set L := Real.log t with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le htpos]
    have := Real.exp_one_lt_d9; linarith
  have hLpos : 0 < L := by linarith
  set v := Real.log L with hv
  have hvle : v ≤ L / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < L / Real.exp 1 by positivity)
    rw [Real.log_div hLpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    linarith
  have hv0 : 0 ≤ v := Real.log_nonneg hL1
  have hf : f₁ t = L + 3 * v := by
    unfold f₁; rw [if_neg (by omega)]
  have hexp : Real.exp (-(L + 3 * v)) = 1 / (t * L ^ 3) := by
    have eL : Real.exp L = t := by rw [hLdef]; exact Real.exp_log htpos
    have ev : Real.exp v = L := by rw [hv]; exact Real.exp_log hLpos
    rw [Real.exp_neg, show L + 3 * v = L + v + v + v by ring, Real.exp_add, Real.exp_add,
      Real.exp_add, eL, ev, one_div]
    ring
  have hceil : (⌈f₁ t * Real.log t⌉₊ : ℝ) ≤ (L + 3 * v) * L + 1 := by
    rw [hf]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have he2 : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hpoly : (L + 3 * v) * L + 1 ≤ 4 * L ^ 2 := by
    have h3v : 3 * v * L ≤ 3 * L ^ 2 / 2 := by
      have : v ≤ L / 2 := by
        refine hvle.trans ?_
        rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]; nlinarith
      nlinarith
    nlinarith
  have hstep := loglog_step t htR
  rw [← hLdef] at hstep
  unfold c1term
  rw [hf, hexp]
  calc Real.exp 1 * (⌈(L + 3 * v) * L⌉₊ : ℝ) * (1 / (t * L ^ 3))
      ≤ Real.exp 1 * (4 * L ^ 2) * (1 / (t * L ^ 3)) := by
        gcongr
        rw [← hf]; exact hceil.trans hpoly
    _ = 4 * Real.exp 1 * (1 / (t * L)) := by field_simp
    _ ≤ _ := by gcongr

lemma c1term_small : c1term 2 + c1term 3 ≤ 3 + 4 * Real.exp 1 * Real.log (Real.log 3) := by
  obtain ⟨hu1, hu2⟩ := log_three_bounds
  set u := Real.log 3 with hu
  set v := Real.log u with hv
  have hupos : 0 < u := by linarith
  have hv1 : 1 - 1 / 1.09 ≤ v := by
    have := Real.one_sub_inv_le_log_of_pos hupos
    have : 1 / u ≤ 1 / 1.09 := one_div_le_one_div_of_le (by norm_num) hu1.le
    rw [inv_eq_one_div] at *; linarith
  have hv2 : v ≤ 0.1 := by have := Real.log_le_sub_one_of_pos hupos; linarith
  have hf2 : f₁ 2 = u + 3 * v := by unfold f₁; simp [hu, hv]
  have hf3 : f₁ 3 = u + 3 * v := by unfold f₁; simp [hu, hv]
  have hexp : Real.exp (-(u + 3 * v)) = 1 / (3 * u ^ 3) := by
    have eu : Real.exp u = 3 := by rw [hu]; exact Real.exp_log (by norm_num)
    have ev : Real.exp v = u := by rw [hv]; exact Real.exp_log hupos
    rw [Real.exp_neg, show u + 3 * v = u + v + v + v by ring, Real.exp_add, Real.exp_add,
      Real.exp_add, eu, ev, one_div]
    ring
  have hl2 := Real.log_two_lt_d9
  have hL3 : u + 3 * v ≤ 1.4 := by linarith
  have hL3' : 0 ≤ u + 3 * v := by linarith
  have hc2 : (⌈(u + 3 * v) * Real.log 2⌉₊ : ℝ) ≤ (u + 3 * v) * Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hc3 : (⌈(u + 3 * v) * u⌉₊ : ℝ) ≤ (u + 3 * v) * u + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hnum : (u + 3 * v) * Real.log 2 + 1 + ((u + 3 * v) * u + 1) ≤ 4.52 := by
    have : (u + 3 * v) * (Real.log 2 + u) ≤ 1.4 * (0.6931471808 + 1.1) :=
      mul_le_mul hL3 (by linarith) (by positivity) (by norm_num)
    nlinarith
  have hden : 1 / (3 * u ^ 3) ≤ 1 / 3.8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1.09:ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu1.le 3
    nlinarith
  have he := Real.exp_one_lt_d9
  have hepos := Real.exp_pos 1
  unfold c1term
  rw [hf2, hf3, hexp]
  push_cast
  have hc3' : (⌈(u + 3 * v) * Real.log 3⌉₊ : ℝ) ≤ (u + 3 * v) * u + 1 := by rw [← hu]; exact hc3
  calc Real.exp 1 * (⌈(u + 3 * v) * Real.log 2⌉₊ : ℝ) * (1 / (3 * u ^ 3)) +
        Real.exp 1 * (⌈(u + 3 * v) * Real.log 3⌉₊ : ℝ) * (1 / (3 * u ^ 3))
      = Real.exp 1 * ((⌈(u + 3 * v) * Real.log 2⌉₊ : ℝ) + (⌈(u + 3 * v) * Real.log 3⌉₊ : ℝ)) *
          (1 / (3 * u ^ 3)) := by ring
    _ ≤ Real.exp 1 * 4.52 * (1 / 3.8) := by
        gcongr
        linarith
    _ ≤ 3 + 4 * Real.exp 1 * v := by nlinarith

lemma c1_numeric (T : ℕ) (hT : 3 ≤ T) :
    ∑ t ∈ Finset.Ico 2 T, c1term t ≤ 4 * Real.exp 1 * Real.log (Real.log T) + 3 := by
  have hsmall := c1term_small
  have hl3 : 0 < Real.log (Real.log 3) := by
    obtain ⟨h1, _⟩ := log_three_bounds
    exact Real.log_pos (by linarith)
  have he := Real.exp_pos 1
  -- induction for T ≥ 4
  have key : ∀ n : ℕ, ∑ t ∈ Finset.Ico 2 (n + 4), c1term t ≤
      c1term 2 + c1term 3 + 4 * Real.exp 1 *
        (Real.log (Real.log ((n + 4 : ℕ) - 1 : ℝ)) - Real.log (Real.log 3)) := by
    intro n
    induction n with
    | zero =>
      have : Finset.Ico 2 (0 + 4) = {2, 3} := by decide
      rw [this, Finset.sum_pair (by norm_num)]
      norm_num
    | succ k ih =>
      rw [show k + 1 + 4 = (k + 4) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
      have hstep := c1term_le (k + 4) (by omega)
      have e : (((k + 4 + 1 : ℕ) : ℝ) - 1) = ((k + 4 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      linarith
  rcases Nat.lt_or_ge T 4 with h | h
  · have : T = 3 := by omega
    subst this
    have : Finset.Ico 2 3 = {2} := by decide
    rw [this, Finset.sum_singleton]
    have := c1term_nonneg 3
    push_cast
    linarith
  · obtain ⟨n, rfl⟩ : ∃ n, T = n + 4 := ⟨T - 4, by omega⟩
    refine (key n).trans ?_
    have hmono : Real.log (Real.log ((n + 4 : ℕ) - 1 : ℝ)) ≤ Real.log (Real.log ((n + 4 : ℕ) : ℝ)) := by
      have h3 : (3 : ℝ) ≤ ((n + 4 : ℕ) : ℝ) - 1 := by push_cast; linarith
      apply Real.log_le_log (Real.log_pos (by linarith))
      exact Real.log_le_log (by linarith) (by linarith)
    nlinarith

/-- C1 from the deviation inequality (13), taken as a hypothesis. -/
theorem optimal_index_sum_of_dev {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hrun : IsKLUCBRun F f₁ X I)
    (astar : Fin K) (hastar : μ astar = bestMean μ) (T : ℕ) (hT : 3 ≤ T)
    (hdev : ∀ (ε : ℝ), 1 < ε → ∀ t : ℕ, 2 ≤ t →
      P {ω | 1 ≤ pullCount I astar t ω ∧
        sampleMean X astar (pullCount I astar t ω) ω < bestMean μ ∧
        ENNReal.ofReal (ε / (pullCount I astar t ω : ℝ)) ≤
          dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ)} ≤
      ENNReal.ofReal (Real.exp 1 * (⌈ε * Real.log t⌉₊ : ℝ) * Real.exp (-ε))) :
    ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ bestMean μ} ≤
      4 * Real.exp 1 * Real.log (Real.log T) + 3 := by
  have hbest : bestMean μ = deriv F.b (θ astar) := by
    rw [← hastar]; exact arm_mean_mem F P X μ hX θ hθ hlaw astar
  have h2 := hθ astar
  have hpt : ∀ t ∈ Finset.Ico K T,
      P.real {ω | klucbIndex F f₁ X I astar t ω ≤ bestMean μ} ≤ c1term t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hsub : {ω | klucbIndex F f₁ X I astar t ω ≤ bestMean μ} ⊆
        {ω | 1 ≤ pullCount I astar t ω ∧
          sampleMean X astar (pullCount I astar t ω) ω < bestMean μ ∧
          ENNReal.ofReal (f₁ t / (pullCount I astar t ω : ℝ)) ≤
            dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hN := (pullCount_bounds hrun astar t ht.1 ω).1
      have hNpos : (0:ℝ) < pullCount I astar t ω := by exact_mod_cast hN
      have hγ : 0 < f₁ t / (pullCount I astar t ω : ℝ) := div_pos (f₁_pos t) hNpos
      have hU : klIndex F (sampleMean X astar (pullCount I astar t ω) ω)
          (f₁ t / (pullCount I astar t ω : ℝ)) ≤ deriv F.b (θ astar) := by
        rw [← hbest]; exact hω
      have hd : ENNReal.ofReal (f₁ t / (pullCount I astar t ω : ℝ)) ≤
          dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ) := by
        by_contra hc
        push Not at hc
        rw [hbest] at hc
        have := klIndex_gt F hnat h2 hc
        linarith
      refine ⟨hN, ?_, hd⟩
      have hle : sampleMean X astar (pullCount I astar t ω) ω ≤
          klIndex F (sampleMean X astar (pullCount I astar t ω) ω)
            (f₁ t / (pullCount I astar t ω : ℝ)) :=
        le_csSup (klIndex_bdd F hnat _ _) (Or.inr rfl)
      rcases lt_or_eq_of_le (hle.trans hU) with hlt | heq
      · rw [hbest]; exact hlt
      · exfalso
        rw [heq, hbest, dExt_self F h2, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hd
        linarith
    refine (measureReal_mono hsub).trans ?_
    have hP := hdev (f₁ t) (f₁_gt_one t) t (by omega)
    have hnn : 0 ≤ c1term t := c1term_nonneg t
    calc P.real _ = (P _).toReal := rfl
      _ ≤ (ENNReal.ofReal (c1term t)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
      _ = c1term t := ENNReal.toReal_ofReal hnn
  refine (Finset.sum_le_sum hpt).trans ?_
  refine le_trans ?_ (c1_numeric T hT)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht; rw [Finset.mem_Ico] at ht ⊢; omega
  · intro t _ _; exact c1term_nonneg t

/-- The parent, with the deviation inequality (13) as a hypothesis. -/
theorem theorem_1_of_dev {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I)
    (hdev : ∀ astar : Fin K, μ astar = bestMean μ → ∀ (ε : ℝ), 1 < ε → ∀ t : ℕ, 2 ≤ t →
      P {ω | 1 ≤ pullCount I astar t ω ∧
        sampleMean X astar (pullCount I astar t ω) ω < bestMean μ ∧
        ENNReal.ofReal (ε / (pullCount I astar t ω : ℝ)) ≤
          dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ)} ≤
      ENNReal.ofReal (Real.exp 1 * (⌈ε * Real.log t⌉₊ : ℝ) * Real.exp (-ε)))
    (a : Fin K) (ha : μ a < bestMean μ) (T : ℕ) (hT : 3 ≤ T) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      Real.log T / F.d (μ a) (bestMean μ)
        + 2 * Real.sqrt (2 * Real.pi * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a)) ^ 2
            / (F.d (μ a) (bestMean μ)) ^ 3)
          * Real.sqrt (Real.log T + 3 * Real.log (Real.log T))
        + (4 * Real.exp 1 + 3 / F.d (μ a) (bestMean μ)) * Real.log (Real.log T)
        + 8 * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a) / F.d (μ a) (bestMean μ)) ^ 2
        + 6 := by
  have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨astar, hastar⟩ := exists_eq_ciSup_of_finite (f := μ)
  have hastar' : μ astar = bestMean μ := by rw [hastar]; rfl
  have hG := gb10_aux hK F hnat P X μ hX θ hθ hlaw I hI hrun a astar hastar' ha (bestMean μ) T
  have h1 := optimal_index_sum_of_dev hK F hnat P X μ hX θ hθ hlaw I hrun astar hastar' T hT
    (hdev astar hastar')
  have h2 := suboptimal_tail_sum hK F hnat P X μ hX θ hθ hlaw a ha T hT
  have hf : f₁ T = Real.log T + 3 * Real.log (Real.log T) := by
    unfold f₁
    split_ifs with h
    · have : T = 3 := by omega
      subst this; norm_num
    · rfl
  rw [hf] at hG h2
  have hdiv : (Real.log T + 3 * Real.log (Real.log T)) / F.d (μ a) (bestMean μ) =
      Real.log T / F.d (μ a) (bestMean μ) +
        3 / F.d (μ a) (bestMean μ) * Real.log (Real.log T) := by ring
  linarith [hdiv]

/-- The exponential martingale `W_i = exp(l S_{i+1} - (i+1) φ)` of an independent sequence. -/
noncomputable def expMart {Ω : Type*} (Y : ℕ → Ω → ℝ) (l φ : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  Real.exp (l * (∑ k ∈ Finset.range (i + 1), Y k ω) - (i + 1 : ℝ) * φ)

lemma expMart_succ {Ω : Type*} (Y : ℕ → Ω → ℝ) (l φ : ℝ) (i : ℕ) :
    expMart Y l φ (i + 1) = expMart Y l φ i * fun ω => Real.exp (l * Y (i + 1) ω - φ) := by
  funext ω
  simp only [expMart, Pi.mul_apply]
  rw [← Real.exp_add, Finset.sum_range_succ]
  congr 1
  push_cast
  ring

lemma expMart_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k)) {l φ : ℝ}
    (hint : ∀ k, Integrable (fun ω => Real.exp (l * Y k ω)) P) (i : ℕ) :
    Integrable (expMart Y l φ i) P := by
  have h := hind.integrable_exp_mul_sum (t := l) hmeas (s := Finset.range (i + 1))
    (fun k _ => hint k)
  have h2 := h.mul_const (Real.exp (-((i + 1 : ℝ) * φ)))
  refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [expMart, Finset.sum_apply]
  rw [← Real.exp_add]
  ring_nf

lemma expMart_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k)) {l φ : ℝ}
    (hmgf : ∀ k, mgf (Y k) P l = Real.exp φ) (i : ℕ) :
    ∫ ω, expMart Y l φ i ω ∂P = 1 := by
  have hsum : mgf (∑ k ∈ Finset.range (i + 1), Y k) P l = Real.exp φ ^ (i + 1) := by
    rw [hind.mgf_sum hmeas]
    simp [hmgf]
  have e : (fun ω => expMart Y l φ i ω) =
      fun ω => Real.exp (l * (∑ k ∈ Finset.range (i + 1), Y k) ω) * Real.exp (-((i + 1 : ℝ) * φ)) := by
    funext ω
    simp only [expMart, Finset.sum_apply]
    rw [← Real.exp_add]
    ring_nf
  rw [e, integral_mul_const]
  have : ∫ ω, Real.exp (l * (∑ k ∈ Finset.range (i + 1), Y k) ω) ∂P =
      mgf (∑ k ∈ Finset.range (i + 1), Y k) P l := rfl
  rw [this, hsum, ← Real.exp_nat_mul, ← Real.exp_add]
  push_cast
  ring_nf
  exact Real.exp_zero

/-- The exponential martingale is a martingale for the natural filtration. -/
lemma expMart_martingale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k)) {l φ : ℝ}
    (hint : ∀ k, Integrable (fun ω => Real.exp (l * Y k ω)) P)
    (hmgf : ∀ k, mgf (Y k) P l = Real.exp φ) :
    Martingale (expMart Y l φ)
      (Filtration.natural Y fun k => (hmeas k).stronglyMeasurable) P := by
  set ℱ := Filtration.natural Y fun k => (hmeas k).stronglyMeasurable with hℱ
  have hY : ∀ k i, k ≤ i → Measurable[ℱ i] (Y k) := by
    intro k i hki
    have h0 : StronglyMeasurable[ℱ k] (Y k) := Filtration.stronglyAdapted_natural _ k
    exact (h0.mono (ℱ.mono hki)).measurable
  have hadp : StronglyAdapted ℱ (expMart Y l φ) := by
    intro i
    apply Measurable.stronglyMeasurable
    unfold expMart
    apply Measurable.exp
    apply Measurable.sub_const
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun k hk => hY k i (by
      rw [Finset.mem_range] at hk; omega))
  have hZint : ∀ i, Integrable (fun ω => Real.exp (l * Y i ω - φ)) P := by
    intro i
    refine ((hint i).mul_const (Real.exp (-φ))).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  have hZmean : ∀ i, ∫ ω, Real.exp (l * Y i ω - φ) ∂P = 1 := by
    intro i
    have : (fun ω => Real.exp (l * Y i ω - φ)) = fun ω => Real.exp (l * Y i ω) * Real.exp (-φ) := by
      funext ω; rw [← Real.exp_add]; ring_nf
    rw [this, integral_mul_const]
    have h2 : ∫ ω, Real.exp (l * Y i ω) ∂P = mgf (Y i) P l := rfl
    rw [h2, hmgf, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply martingale_nat hadp (expMart_integrable hind hmeas hint)
  intro i
  rw [expMart_succ]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (μ := P) (hadp i)
    (by rw [← expMart_succ]; exact expMart_integrable hind hmeas hint (i + 1)) (hZint (i + 1))
  have hindep : Indep (MeasurableSpace.comap (Y (i + 1)) inferInstance) (ℱ i) P := by
    have h := indep_iSup_of_disjoint (m := fun k => MeasurableSpace.comap (Y k) inferInstance)
      (fun k => (hmeas k).comap_le)
      ((iIndepFun_iff_iIndep (fun _ => inferInstance) Y P).mp hind)
      (S := {i + 1}) (T := Set.Iic i) (by
        rw [Set.disjoint_singleton_left, Set.mem_Iic]; omega)
    have e1 : (⨆ k ∈ ({i + 1} : Set ℕ), MeasurableSpace.comap (Y k) inferInstance) =
        MeasurableSpace.comap (Y (i + 1)) inferInstance := by simp
    have e2 : (⨆ k ∈ Set.Iic i, MeasurableSpace.comap (Y k) inferInstance) = ℱ i := by
      rw [hℱ]; rfl
    rw [e1, e2] at h
    exact h
  have hZsm : StronglyMeasurable[MeasurableSpace.comap (Y (i + 1)) inferInstance]
      (fun ω => Real.exp (l * Y (i + 1) ω - φ)) := by
    apply Measurable.stronglyMeasurable
    exact (((comap_measurable (Y (i + 1))).const_mul l).sub_const φ).exp
  have hce := condExp_indep_eq (hmeas (i + 1)).comap_le (ℱ.le i) hZsm hindep
  rw [hZmean] at hce
  filter_upwards [hpull, hce] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, mul_one]

/-- Doob's maximal inequality for the exponential martingale. -/
lemma expMart_maximal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k)) {l φ : ℝ}
    (hint : ∀ k, Integrable (fun ω => Real.exp (l * Y k ω)) P)
    (hmgf : ∀ k, mgf (Y k) P l = Real.exp φ) (N : ℕ) {A : ℝ} (hA : 0 < A) :
    P {ω | ∃ n ∈ Finset.Icc 1 N, A ≤ Real.exp (l * (∑ k ∈ Finset.range n, Y k ω) - n * φ)} ≤
      ENNReal.ofReal (1 / A) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : {ω | ∃ n ∈ Finset.Icc 1 0, A ≤ Real.exp (l * (∑ k ∈ Finset.range n, Y k ω) - n * φ)} = ∅ := by
      ext ω; simp
    rw [this, measure_empty]; exact zero_le
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hmart := expMart_martingale hind hmeas hint hmgf
  have hnn : 0 ≤ expMart Y l φ := fun i ω => (Real.exp_pos _).le
  set εn : NNReal := ⟨A, hA.le⟩ with hεn
  have hD := maximal_ineq hmart.submartingale hnn (ε := εn) M
  set E := {ω | (εn : ℝ) ≤ (Finset.range (M + 1)).sup' Finset.nonempty_range_add_one
    fun k => expMart Y l φ k ω} with hEdef
  have hsub : {ω | ∃ n ∈ Finset.Icc 1 (M + 1),
      A ≤ Real.exp (l * (∑ k ∈ Finset.range n, Y k ω) - n * φ)} ⊆ E := by
    rintro ω ⟨n, hn, hA'⟩
    rw [Finset.mem_Icc] at hn
    rw [hEdef, Set.mem_setOf_eq]
    have hk : n - 1 ∈ Finset.range (M + 1) := by rw [Finset.mem_range]; omega
    refine le_trans ?_ (Finset.le_sup' (fun k => expMart Y l φ k ω) hk)
    simp only [expMart, hεn]
    have h1 : n - 1 + 1 = n := by omega
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn.1]; push_cast; ring
    rw [h1, hc]; exact hA'
  have hint2 : ∫ ω in E, expMart Y l φ M ω ∂P ≤ 1 := by
    rw [← expMart_integral hind hmeas hmgf M]
    exact setIntegral_le_integral (expMart_integrable hind hmeas hint M)
      (Filter.Eventually.of_forall (fun ω => hnn M ω))
  have hE : (εn : ENNReal) * P E ≤ 1 := by
    refine hD.trans ?_
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hint2
  have hεE : P E ≤ (εn : ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]; exact hE
  refine (measure_mono hsub).trans (hεE.trans (le_of_eq ?_))
  rw [one_div, ENNReal.ofReal_inv_of_pos hA, ENNReal.ofReal_eq_coe_nnreal hA.le]
  exact congrArg (fun x : NNReal => ((x : ENNReal))⁻¹) hεn


/-! ## deviation (13) (session 2) -/

/-- One slice of the peeling: one supporting line of `d(·, μ⋆)` and Doob's inequality. -/
lemma slice_bound {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) {ε c' m0 : ℝ} (hm0 : m0 < deriv F.b (θ a))
    (hd : ENNReal.ofReal c' < dExt F m0 (deriv F.b (θ a))) (N : ℕ) :
    P {ω | ∃ n ∈ Finset.Icc 1 N, ε - 1 ≤ (n : ℝ) * c' ∧ sampleMean X a n ω ≤ m0} ≤
      ENNReal.ofReal (Real.exp (1 - ε)) := by
  have ha := hθ a
  unfold dExt at hd
  rw [θof_deriv F ha] at hd
  obtain ⟨⟨θ0, hθ0⟩, hlt⟩ := lt_iSup_iff.mp hd
  simp only at hlt
  have hg : c' < (θ0 - θ a) * m0 - F.b θ0 + F.b (θ a) := by
    by_contra hc
    push Not at hc
    exact absurd hlt (not_lt.mpr (ENNReal.ofReal_le_ofReal hc))
  have hθlt : θ0 < θ a := by
    by_contra hc
    push Not at hc
    have h1 := expFam_tangent F ha hθ0 hc
    have h2 : (θ0 - θ a) * m0 ≤ (θ0 - θ a) * deriv F.b (θ a) :=
      mul_le_mul_of_nonneg_left hm0.le (by linarith)
    have hc'0 : ENNReal.ofReal c' < ENNReal.ofReal ((θ0 - θ a) * m0 - F.b θ0 + F.b (θ a)) := hlt
    have hpos := (ENNReal.ofReal_lt_ofReal_iff'.mp hc'0).2
    linarith
  set l := θ0 - θ a with hl
  have hθl : θ a + l = θ0 := by rw [hl]; ring
  have hlΘ : θ a + l ∈ F.Θ := by rw [hθl]; exact hθ0
  set φ := F.b (θ a + l) - F.b (θ a) with hφ
  have hind : iIndepFun (fun k : ℕ => X a k) P :=
    hX.indep.precomp (g := fun k : ℕ => (a, k)) (fun i j h => by simpa using h)
  have hmeas : ∀ k, Measurable (X a k) := fun k => hX.measurable a k
  have hint : ∀ k, Integrable (fun ω => Real.exp (l * X a k ω)) P :=
    fun k => (arm_mgf F P X μ hX θ hθ hlaw a k hlΘ).1
  have hmgf : ∀ k, mgf (X a k) P l = Real.exp φ :=
    fun k => (arm_mgf F P X μ hX θ hθ hlaw a k hlΘ).2
  have hmax := expMart_maximal (Y := fun k => X a k) hind hmeas hint hmgf N
    (A := Real.exp (ε - 1)) (Real.exp_pos _)
  have hsub : {ω | ∃ n ∈ Finset.Icc 1 N, ε - 1 ≤ (n : ℝ) * c' ∧ sampleMean X a n ω ≤ m0} ⊆
      {ω | ∃ n ∈ Finset.Icc 1 N, Real.exp (ε - 1) ≤
        Real.exp (l * (∑ k ∈ Finset.range n, X a k ω) - n * φ)} := by
    rintro ω ⟨n, hn, hc, hm⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnpos : (0:ℝ) < n := by linarith
    have hS : (∑ k ∈ Finset.range n, X a k ω) = n * sampleMean X a n ω := by
      unfold sampleMean; field_simp
    rw [hS]
    have hφ' : φ = F.b θ0 - F.b (θ a) := by rw [hφ, hθl]
    have h1 : c' < l * m0 - φ := by rw [hφ', hl]; linarith
    have hl0 : l ≤ 0 := by rw [hl]; linarith
    have h2 : l * m0 ≤ l * sampleMean X a n ω := mul_le_mul_of_nonpos_left hm hl0
    have h3 : (n:ℝ) * c' ≤ n * (l * sampleMean X a n ω - φ) :=
      mul_le_mul_of_nonneg_left (by linarith) hnpos.le
    linarith
  refine (measure_mono hsub).trans (hmax.trans (le_of_eq ?_))
  rw [one_div, ← Real.exp_neg]
  congr 2
  ring

/-- A level set of `d(·, μ⋆)`: union of the slices over a cofinal sequence. -/
lemma level_bound {K : ℕ} (F : ExpFamily) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (a : Fin K) {ε c c' : ℝ} (hc' : 0 < c') (hcc : c' < c) (N : ℕ) :
    P {ω | ∃ n ∈ Finset.Icc 1 N, ε - 1 ≤ (n : ℝ) * c' ∧ sampleMean X a n ω < deriv F.b (θ a) ∧
        ENNReal.ofReal c ≤ dExt F (sampleMean X a n ω) (deriv F.b (θ a))} ≤
      ENNReal.ofReal (Real.exp (1 - ε)) := by
  set μs := deriv F.b (θ a) with hμs
  set S := {m : ℝ | m < μs ∧ ENNReal.ofReal c ≤ dExt F m μs} with hS
  set B : ℝ → Set Ω := fun m0 =>
    {ω | ∃ n ∈ Finset.Icc 1 N, ε - 1 ≤ (n : ℝ) * c' ∧ sampleMean X a n ω ≤ m0} with hB
  have hBmono : Monotone B := by
    intro x y hxy ω hω
    obtain ⟨n, hn, h1, h2⟩ := hω
    exact ⟨n, hn, h1, h2.trans hxy⟩
  have hBS : ∀ m0 ∈ S, P (B m0) ≤ ENNReal.ofReal (Real.exp (1 - ε)) := by
    intro m0 hm0
    exact slice_bound F P X μ hX θ hθ hlaw a hm0.1
      (lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hcc, by linarith⟩) hm0.2) N
  have hsub : {ω | ∃ n ∈ Finset.Icc 1 N, ε - 1 ≤ (n : ℝ) * c' ∧ sampleMean X a n ω < μs ∧
      ENNReal.ofReal c ≤ dExt F (sampleMean X a n ω) μs} ⊆ ⋃ m0 ∈ S, B m0 := by
    rintro ω ⟨n, hn, h1, h2, h3⟩
    exact Set.mem_biUnion (show sampleMean X a n ω ∈ S from ⟨h2, h3⟩) ⟨n, hn, h1, le_rfl⟩
  refine (measure_mono hsub).trans ?_
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe]; simp
  have hbdd : BddAbove S := ⟨μs, fun m hm => hm.1.le⟩
  by_cases hz : sSup S ∈ S
  · have h' : (⋃ m0 ∈ S, B m0) ⊆ B (sSup S) :=
      Set.iUnion₂_subset fun m0 hm0 => hBmono (le_csSup hbdd hm0)
    exact (measure_mono h').trans (hBS _ hz)
  · obtain ⟨u, humono, hutend, huS⟩ := exists_seq_tendsto_sSup hSne hbdd
    have h' : (⋃ m0 ∈ S, B m0) ⊆ ⋃ j, B (u j) := by
      refine Set.iUnion₂_subset fun m0 hm0 => ?_
      have hlt : m0 < sSup S :=
        lt_of_le_of_ne (le_csSup hbdd hm0) (fun h => hz (h ▸ hm0))
      obtain ⟨j, hj⟩ := (hutend.eventually (lt_mem_nhds hlt)).exists
      exact (hBmono hj.le).trans (Set.subset_iUnion (fun j => B (u j)) j)
    refine (measure_mono h').trans ?_
    rw [show (⋃ j, B (u j)) = ⋃ j, (B ∘ u) j from rfl, (hBmono.comp humono).measure_iUnion]
    exact iSup_le fun j => hBS _ (huS j)

/-- (13), Cappé et al., p. 14, for `t ≥ 2`. -/
theorem dev13 {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hadapt : IsNonanticipating X I) (hrun : IsKLUCBRun F f₁ X I)
    (astar : Fin K) (hastar : μ astar = bestMean μ) (ε : ℝ) (hε : 1 < ε) (t : ℕ) (ht : 2 ≤ t) :
    P {ω | 1 ≤ pullCount I astar t ω ∧
        sampleMean X astar (pullCount I astar t ω) ω < bestMean μ ∧
        ENNReal.ofReal (ε / (pullCount I astar t ω : ℝ)) ≤
          dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ)} ≤
      ENNReal.ofReal (Real.exp 1 * (⌈ε * Real.log t⌉₊ : ℝ) * Real.exp (-ε)) := by
  have hbest : bestMean μ = deriv F.b (θ astar) := by
    rw [← hastar]; exact arm_mean_mem F P X μ hX θ hθ hlaw astar
  rw [hbest]
  set μs := deriv F.b (θ astar) with hμs
  have hεpos : 0 < ε := by linarith
  have htR : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  set D := ⌈ε * Real.log t⌉₊ with hD
  have hDpos : 0 < D := Nat.ceil_pos.mpr (mul_pos hεpos hlogt)
  have hDR : ε * Real.log t ≤ D := Nat.le_ceil _
  have hDR0 : (0:ℝ) < D := by exact_mod_cast hDpos
  set r := Real.exp (Real.log t / D) with hr
  have hr1 : 1 < r := by
    have hx := div_pos hlogt hDR0
    have := Real.add_one_lt_exp hx.ne'
    rw [hr]; linarith
  have hrpos : 0 < r := by linarith
  have hrε : r ≤ Real.exp (1 / ε) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ hDR0 hεpos]
    linarith
  have hrD : r ^ D = t := by
    rw [hr, ← Real.exp_nat_mul, show (D:ℝ) * (Real.log t / D) = Real.log t by field_simp,
      Real.exp_log (by linarith)]
  set κ := (ε - 1) * Real.exp (1 / ε) with hκ
  have hκpos : 0 < κ := mul_pos (by linarith) (Real.exp_pos _)
  have hκε : κ < ε := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr (one_div_pos.mpr hεpos).ne')
    have e1 : Real.exp (1 / ε) * Real.exp (-(1 / ε)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : ε - 1 < ε * Real.exp (-(1 / ε)) := by
      have h3 := mul_lt_mul_of_pos_left h hεpos
      have e2 : ε * (-(1 / ε) + 1) = ε - 1 := by field_simp; ring
      linarith
    calc κ = (ε - 1) * Real.exp (1 / ε) := rfl
      _ < ε * Real.exp (-(1 / ε)) * Real.exp (1 / ε) :=
          mul_lt_mul_of_pos_right h2 (Real.exp_pos _)
      _ = ε := by rw [mul_assoc, mul_comm (Real.exp (-(1 / ε))), e1, mul_one]
  set Ev : ℕ → Set Ω := fun k => {ω | ∃ n ∈ Finset.Icc 1 t, ε - 1 ≤ (n : ℝ) * (κ / r ^ k) ∧
      sampleMean X astar n ω < μs ∧
      ENNReal.ofReal (ε / r ^ k) ≤ dExt F (sampleMean X astar n ω) μs} with hEv
  have hEvb : ∀ k, P (Ev k) ≤ ENNReal.ofReal (Real.exp (1 - ε)) := by
    intro k
    have hrk : 0 < r ^ k := pow_pos hrpos k
    exact level_bound F P X μ hX θ hθ hlaw astar (div_pos hκpos hrk)
      (div_lt_div_of_pos_right hκε hrk) t
  have hsub : {ω | 1 ≤ pullCount I astar t ω ∧ sampleMean X astar (pullCount I astar t ω) ω < μs ∧
      ENNReal.ofReal (ε / (pullCount I astar t ω : ℝ)) ≤
        dExt F (sampleMean X astar (pullCount I astar t ω) ω) μs} ⊆
      ⋃ k ∈ Finset.Icc 1 D, Ev k := by
    rintro ω ⟨h1, h2, h3⟩
    have hnt : pullCount I astar t ω ≤ t :=
      (Finset.card_filter_le (Finset.range t) _).trans_eq (Finset.card_range t)
    set n := pullCount I astar t ω with hn
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast h1
    have hex : ∃ k, (n:ℝ) ≤ r ^ k := ⟨D, by rw [hrD]; exact_mod_cast hnt⟩
    classical
    have hk1 : (n:ℝ) ≤ r ^ (Nat.find hex) := Nat.find_spec hex
    have hkD : Nat.find hex ≤ D := Nat.find_min' hex (by rw [hrD]; exact_mod_cast hnt)
    obtain ⟨k', hk'1, hk'D, hup, hlo⟩ : ∃ k', 1 ≤ k' ∧ k' ≤ D ∧ (n:ℝ) ≤ r ^ k' ∧
        r ^ (k' - 1) ≤ n := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hk0
      · refine ⟨1, le_rfl, hDpos, ?_, by simpa using hnR⟩
        rw [hk0] at hk1
        exact hk1.trans (by simpa using hr1.le)
      · refine ⟨Nat.find hex, hk0, hkD, hk1, ?_⟩
        have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        push Not at this
        exact this.le
    refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hk'1, hk'D⟩)) ?_
    refine ⟨n, Finset.mem_Icc.mpr ⟨h1, hnt⟩, ?_, h2, ?_⟩
    · have hrk : r ^ k' = r ^ (k' - 1) * r := by
        rw [← pow_succ]; congr 1; omega
      have hrp : 0 < r ^ (k' - 1) := pow_pos hrpos _
      rw [hrk]
      have h4 : ε - 1 ≤ κ / r := by
        rw [le_div_iff₀ hrpos, hκ]
        exact mul_le_mul_of_nonneg_left hrε (by linarith)
      have h5 : κ / r ≤ (n:ℝ) * (κ / (r ^ (k' - 1) * r)) := by
        rw [show (n:ℝ) * (κ / (r ^ (k' - 1) * r)) = (n / r ^ (k' - 1)) * (κ / r) by
          field_simp]
        have h6 : 1 ≤ (n:ℝ) / r ^ (k' - 1) := by rw [le_div_iff₀ hrp]; linarith
        have h7 : 0 ≤ κ / r := (div_pos hκpos hrpos).le
        nlinarith
      linarith
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
      exact div_le_div_of_nonneg_left hεpos.le (by linarith) hup
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ k ∈ Finset.Icc 1 D, P (Ev k) ≤ ∑ k ∈ Finset.Icc 1 D, ENNReal.ofReal (Real.exp (1 - ε)) :=
        Finset.sum_le_sum fun k _ => hEvb k
    _ = ENNReal.ofReal (Real.exp 1 * (D : ℝ) * Real.exp (-ε)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, add_tsub_cancel_right,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg D)]
        congr 1
        rw [show (1 - ε) = 1 + (-ε) by ring, Real.exp_add]
        ring

end CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic OptimalBAI.OptProportions CappeKLUCB.ExpFam in
theorem solution {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hadapt : IsNonanticipating X I) (hrun : IsKLUCBRun F f₁ X I)
    (a : Fin K) (ha : μ a < bestMean μ) (T : ℕ) (hT : 3 ≤ T) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      Real.log T / F.d (μ a) (bestMean μ)
        + 2 * Real.sqrt (2 * Real.pi * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a)) ^ 2
            / (F.d (μ a) (bestMean μ)) ^ 3)
          * Real.sqrt (Real.log T + 3 * Real.log (Real.log T))
        + (4 * Real.exp 1 + 3 / F.d (μ a) (bestMean μ)) * Real.log (Real.log T)
        + 8 * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a) / F.d (μ a) (bestMean μ)) ^ 2
        + 6 := by
  exact theorem_1_of_dev hK F hnat P X μ hX θ hθ hlaw I hI hrun
    (fun astar h ε hε t ht => dev13 hK F hnat P X μ hX θ hθ hlaw I hI hadapt hrun astar h ε hε t ht)
    a ha T hT
