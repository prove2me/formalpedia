-- Prove2me | solution 1 for CappeKLUCB.ExpFam.general_bound_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:38:04.797563+00:00
-- url     : https://prove2.me/submissions/8c5e12ca-c739-403b-b723-48a225eb292c

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

end CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic OptimalBAI.OptProportions CappeKLUCB.ExpFam in
theorem solution {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
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
  exact CappeKLUCB.ExpFam.gb10_aux hK F hnat P X μ hX θ hθ hlaw I hI hrun a astar hastar ha μdag T
