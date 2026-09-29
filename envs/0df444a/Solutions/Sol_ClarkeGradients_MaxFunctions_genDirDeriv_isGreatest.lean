-- Prove2me | solution 1 for ClarkeGradients.MaxFunctions.genDirDeriv_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:27:12.747391+00:00
-- url     : https://prove2.me/submissions/066358d5-bc1b-48f6-8f9d-b32982e66945

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv

open Filter Topology Set Metric MeasureTheory

namespace ClarkeGradients.MaxFunctions

/-- For a Lipschitz function, a.e. line in direction `v` meets the non-differentiability set
in a null set. -/
theorem aux_gdg_ae_line {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) (v : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ y : EuclideanSpace ℝ (Fin n), ∀ᵐ t : ℝ, DifferentiableAt ℝ F (y + t • v) := by
  have hN : volume {z | ¬ DifferentiableAt ℝ F z} = 0 := by
    have := hF.ae_differentiableAt (μ := volume)
    rwa [ae_iff] at this
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hN
  have hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 + p.2 • v ∉ N} := by
    have : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1 + p.2 • v) :=
      measurable_fst.add (measurable_snd.smul_const v)
    exact (this hNm).compl
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ y : EuclideanSpace ℝ (Fin n), y + t • v ∉ N := by
    refine ae_of_all _ (fun t => ?_)
    have : volume ((fun y => y + t • v) ⁻¹' N) = 0 := by
      rw [measure_preimage_add_right]; exact hN0
    exact measure_eq_zero_iff_ae_notMem.1 this
  have h2 := (Measure.ae_ae_comm hmeas).2 h1
  filter_upwards [h2] with y hy
  filter_upwards [hy] with t ht
  by_contra hc
  exact ht (hsub hc)

/-- One-dimensional estimate along a good line. -/
theorem aux_gdg_line {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) (v y : EuclideanSpace ℝ (Fin n)) (c δ : ℝ) (hδ : 0 ≤ δ)
    (hae : ∀ᵐ t : ℝ, DifferentiableAt ℝ F (y + t • v))
    (hc : ∀ t ∈ Icc 0 δ, DifferentiableAt ℝ F (y + t • v) → fderiv ℝ F (y + t • v) v ≤ c) :
    F (y + δ • v) - F y ≤ c * δ := by
  set g : ℝ → ℝ := fun t => F (y + t • v) with hg
  have h2 : LipschitzWith ‖v‖₊ (fun t : ℝ => y + t • v) := by
    refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
    rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]
    rfl
  have hgL : LipschitzWith (K * ‖v‖₊) g := hF.comp h2
  have hac : AbsolutelyContinuousOnInterval g 0 δ :=
    (hgL.lipschitzOnWith (s := uIcc 0 δ)).absolutelyContinuousOnInterval
  have hftc := hac.integral_deriv_eq_sub
  have hderiv : ∀ t, DifferentiableAt ℝ F (y + t • v) →
      HasDerivAt g (fderiv ℝ F (y + t • v) v) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => y + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    exact ht.hasFDerivAt.comp_hasDerivAt t h1
  have hle : (∫ t in (0:ℝ)..δ, deriv g t) ≤ ∫ _ in (0:ℝ)..δ, c := by
    refine intervalIntegral.integral_mono_ae_restrict hδ hac.intervalIntegrable_deriv
      intervalIntegrable_const ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with t ht htI
    rw [(hderiv t ht).deriv]
    exact hc t htI ht
  have e1 : g δ = F (y + δ • v) := rfl
  have e0 : g 0 = F y := by simp [hg]
  rw [hftc, intervalIntegral.integral_const, smul_eq_mul, e1, e0] at hle
  linarith

/-- Core estimate: a bound on directional derivatives at differentiability points near a segment
bounds the increment along the segment. -/
theorem aux_gdg_core {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) (v y : EuclideanSpace ℝ (Fin n)) (c δ ρ : ℝ) (hδ : 0 ≤ δ)
    (hρ : 0 < ρ)
    (hc : ∀ y' ∈ ball y ρ, ∀ t ∈ Icc 0 δ, DifferentiableAt ℝ F (y' + t • v) →
      fderiv ℝ F (y' + t • v) v ≤ c) :
    F (y + δ • v) - F y ≤ c * δ := by
  by_contra hlt
  push Not at hlt
  set W := ball y ρ ∩ {y' | c * δ < F (y' + δ • v) - F y'} with hW
  have hWo : IsOpen W := by
    refine isOpen_ball.inter (isOpen_lt continuous_const ?_)
    exact (hF.continuous.comp (continuous_id.add continuous_const)).sub hF.continuous
  have hyW : y ∈ W := ⟨mem_ball_self hρ, hlt⟩
  have hpos : volume W ≠ 0 := (hWo.measure_pos volume ⟨y, hyW⟩).ne'
  apply hpos
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [aux_gdg_ae_line hF v] with y' hy' hy'W
  have := aux_gdg_line hF v y' c δ hδ hy' (fun t ht hd => hc y' hy'W.1 t ht hd)
  exact absurd hy'W.2 (not_lt.2 this)

/-- The statement for a globally Lipschitz function. -/
theorem aux_gdg_main {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : NNReal}
    (hF : LipschitzWith K F) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' Shared.generalizedGradient F x)
      (Shared.genDirDeriv F x v) := by
  set q : EuclideanSpace ℝ (Fin n) × ℝ → ℝ :=
    fun p => (F (x + p.1 + p.2 • v) - F (x + p.1)) / p.2 with hq
  set 𝓕 := (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)) with h𝓕
  have hL : Shared.genDirDeriv F x v = limsup q 𝓕 := rfl
  set L := Shared.genDirDeriv F x v with hLdef
  have hpos : ∀ᶠ p in 𝓕, 0 < p.2 := Filter.Eventually.prod_inr self_mem_nhdsWithin _
  have hbd : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → |q p| ≤ K * ‖v‖ := by
    intro p hp
    simp only [hq]
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have := hF.dist_le_mul (x + p.1 + p.2 • v) (x + p.1)
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hp] at this
    linarith
  have hub : IsBoundedUnder (· ≤ ·) 𝓕 q :=
    isBoundedUnder_of_eventually_le (a := K * ‖v‖)
      (hpos.mono fun p hp => (abs_le.1 (hbd p hp)).2)
  have hcob : IsCoboundedUnder (· ≤ ·) 𝓕 q :=
    isCoboundedUnder_le_of_eventually_le 𝓕 (x := -(K * ‖v‖))
      (hpos.mono fun p hp => (abs_le.1 (hbd p hp)).1)
  have hgradv : ∀ y, inner ℝ (gradient F y) v = fderiv ℝ F y v := fun y => inner_gradient_left
  -- upper bound on the gradient limits
  have hG_ub : ∀ ζ ∈ Shared.gradientLimits F x, inner ℝ ζ v ≤ L := by
    rintro ζ ⟨h, hh0, hdiff, hlim⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hLc, hcz⟩ := exists_between hcon
    have hev := eventually_lt_of_limsup_lt (hL ▸ hLc) hub
    rw [h𝓕, eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hall⟩ := hev
    have hlim' : Tendsto (fun i => inner ℝ (gradient F (x + h i)) v) atTop
        (𝓝 (inner ℝ ζ v)) := hlim.inner tendsto_const_nhds
    obtain ⟨i, hi1, hi2⟩ := ((hh0.eventually hpa).and (hlim'.eventually (lt_mem_nhds hcz))).exists
    set y := x + h i with hy
    have hd : HasDerivAt (fun t : ℝ => F (y + t • v)) (fderiv ℝ F y v) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
      have hdy : HasFDerivAt F (fderiv ℝ F y) (y + (0:ℝ) • v) := by
        rw [zero_smul, add_zero]; exact (hdiff i).hasFDerivAt
      exact hdy.comp_hasDerivAt (0:ℝ) h1
    have hsl := hd.tendsto_slope_zero_right
    rw [← hgradv] at hsl
    have hev2 := hsl.eventually (lt_mem_nhds hi2)
    obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((hev2.and hpb).and self_mem_nhdsWithin).exists
    have hq' := hall hi1 ht2
    simp only [hq] at hq'
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht1
    have ht3' : 0 < t := ht3
    rw [div_eq_inv_mul] at hq'
    linarith
  -- near-maximizers of the directional derivative
  have hnear : ∀ r > 0, ∀ ε > 0, ∃ y, ‖y - x‖ < r ∧ DifferentiableAt ℝ F y ∧
      L - ε < fderiv ℝ F y v := by
    intro r hr ε hε
    by_contra H
    push Not at H
    have hev : ∀ᶠ p in 𝓕, q p ≤ L - ε := by
      have hb : (0:ℝ) < r / (3 * (‖v‖ + 1)) := by positivity
      filter_upwards [prod_mem_prod (ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n))
        (by positivity : (0:ℝ) < r / 3)) (Ioo_mem_nhdsGT hb)] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : ‖p.1‖ < r / 3 := by simpa using hp1
      have hp2' : p.2 * (‖v‖ + 1) < r / 3 := by
        have := hp2.2
        rw [lt_div_iff₀ (by positivity)] at this
        linarith
      have hcore := aux_gdg_core hF v (x + p.1) (L - ε) p.2 (r / 3) hp2.1.le (by positivity) ?_
      · simp only [hq]
        rw [div_le_iff₀ hp2.1]
        linarith [hcore]
      · intro y' hy' t ht hdiff
        apply H _ _ hdiff
        have hy'' : ‖y' - (x + p.1)‖ < r / 3 := by simpa [dist_eq_norm] using hy'
        have htv : ‖t • v‖ < r / 3 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          nlinarith [ht.2, norm_nonneg v, ht.1]
        calc ‖y' + t • v - x‖ = ‖(y' - (x + p.1)) + p.1 + t • v‖ := by congr 1; abel
          _ ≤ ‖y' - (x + p.1)‖ + ‖p.1‖ + ‖t • v‖ := norm_add₃_le
          _ < r := by linarith
    have := limsup_le_of_le hcob hev
    rw [← hL] at this
    linarith
  have hseq : ∀ k : ℕ, ∃ y, ‖y - x‖ < 1 / ((k:ℝ) + 1) ∧ DifferentiableAt ℝ F y ∧
      L - 1 / ((k:ℝ) + 1) < fderiv ℝ F y v :=
    fun k => hnear _ Nat.one_div_pos_of_nat _ Nat.one_div_pos_of_nat
  choose y hy1 hy2 hy3 using hseq
  have hgb : ∀ k, gradient F (y k) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) K := by
    intro k
    rw [mem_closedBall, dist_zero_right]
    simp only [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hF
  obtain ⟨ζ₀, -, φ, hφ, hlimζ⟩ := tendsto_subseq_of_bounded isBounded_closedBall hgb
  have hy0 : Tendsto (fun k => y k - x) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (hy1 k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hζ₀G : ζ₀ ∈ Shared.gradientLimits F x := by
    refine ⟨fun k => y (φ k) - x, hy0.comp hφ.tendsto_atTop, fun k => by simpa using hy2 (φ k),
      ?_⟩
    refine hlimζ.congr (fun k => ?_)
    simp
  have hζ₀v : L ≤ inner ℝ ζ₀ v := by
    have h1 : Tendsto (fun k => inner ℝ (gradient F (y (φ k))) v) atTop (𝓝 (inner ℝ ζ₀ v)) :=
      hlimζ.inner tendsto_const_nhds
    have h2 : Tendsto (fun k => L - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (L - 0)) :=
      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    rw [sub_zero] at h2
    exact le_of_tendsto_of_tendsto' h2 h1 (fun k => by rw [hgradv]; exact (hy3 (φ k)).le)
  have hconv : Convex ℝ {ζ : EuclideanSpace ℝ (Fin n) | inner ℝ ζ v ≤ L} :=
    convex_halfSpace_le ⟨fun a b => inner_add_left a b v, fun r a => real_inner_smul_left a v r⟩ L
  have hco : Shared.generalizedGradient F x ⊆ {ζ | inner ℝ ζ v ≤ L} :=
    convexHull_min hG_ub hconv
  refine ⟨⟨ζ₀, subset_convexHull ℝ _ hζ₀G, le_antisymm (hG_ub ζ₀ hζ₀G) hζ₀v⟩, ?_⟩
  rintro s ⟨ζ, hζ, rfl⟩
  exact hco hζ

theorem aux_gdg_gl_sub {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hfg : ∀ z ∈ ball x r, f =ᶠ[𝓝 z] g) (hr : 0 < r) :
    Shared.gradientLimits f x ⊆ Shared.gradientLimits g x := by
  rintro ζ ⟨h, hh0, hdiff, hlim⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hh0.eventually (ball_mem_nhds 0 hr))
  have hz : ∀ i, x + h (i + N) ∈ ball x r := by
    intro i
    have := hN (i + N) (by omega)
    simpa [mem_ball, dist_eq_norm] using this
  refine ⟨fun i => h (i + N), (tendsto_add_atTop_iff_nat N).2 hh0, fun i => ?_, ?_⟩
  · exact (hfg _ (hz i)).differentiableAt_iff.1 (hdiff _)
  · have : Tendsto (fun i => gradient f (x + h (i + N))) atTop (𝓝 ζ) :=
      (tendsto_add_atTop_iff_nat (f := fun i => gradient f (x + h i)) N).2 hlim
    refine this.congr (fun i => ?_)
    exact (hfg _ (hz i)).gradient_eq

end ClarkeGradients.MaxFunctions

open ClarkeGradients.MaxFunctions

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ClarkeGradients.Shared.LipschitzOnBounded f) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' ClarkeGradients.Shared.generalizedGradient f x)
      (ClarkeGradients.Shared.genDirDeriv f x v) := by
  obtain ⟨K, hK⟩ := hf (closedBall x 2) isBounded_closedBall
  obtain ⟨F, hF, hEq⟩ := hK.extend_real
  have hloc : ∀ z ∈ ball x 1, f =ᶠ[𝓝 z] F := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hEq (ball_subset_closedBall (ball_subset_ball (by norm_num) hw))
  have hGG : ClarkeGradients.Shared.generalizedGradient f x =
      ClarkeGradients.Shared.generalizedGradient F x := by
    unfold ClarkeGradients.Shared.generalizedGradient
    rw [Set.Subset.antisymm (aux_gdg_gl_sub hloc one_pos)
      (aux_gdg_gl_sub (fun z hz => (hloc z hz).symm) one_pos)]
  have hDD : ClarkeGradients.Shared.genDirDeriv f x v =
      ClarkeGradients.Shared.genDirDeriv F x v := by
    unfold ClarkeGradients.Shared.genDirDeriv
    apply limsup_congr
    have hb : (0:ℝ) < 1 / (‖v‖ + 1) := by positivity
    filter_upwards [prod_mem_prod (ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) one_pos)
      (Ioo_mem_nhdsGT hb)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : ‖p.1‖ < 1 := by simpa using hp1
    have hp2' : ‖p.2 • v‖ < 1 := by
      have := hp2.2
      rw [lt_div_iff₀ (by positivity)] at this
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp2.1]
      nlinarith [norm_nonneg v, hp2.1]
    have h1 : x + p.1 ∈ closedBall x 2 := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; linarith
    have h2 : x + p.1 + p.2 • v ∈ closedBall x 2 := by
      rw [mem_closedBall, dist_eq_norm, add_assoc, add_sub_cancel_left]
      linarith [norm_add_le p.1 (p.2 • v)]
    rw [hEq h1, hEq h2]
  rw [hGG, hDD]
  exact aux_gdg_main hF x v
