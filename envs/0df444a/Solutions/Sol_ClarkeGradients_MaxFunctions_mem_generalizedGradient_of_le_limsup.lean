-- Prove2me | solution 1 for ClarkeGradients.MaxFunctions.mem_generalizedGradient_of_le_limsup
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:55:03.216098+00:00
-- url     : https://prove2.me/submissions/d43a2f38-cce4-40f6-96ec-778e1d395d1c

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

open Filter Topology

namespace ClarkeGradients.MaxFunctions

open MeasureTheory Metric Set

/-- The convex hull of a compact set in a finite-dimensional space is compact. -/
lemma aux_mgl_isCompact_convexHull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  set d := Module.finrank ℝ E
  let Φ : (Fin (d+1) → ℝ) × (Fin (d+1) → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hΦ : Continuous Φ := by
    unfold Φ
    fun_prop
  have hD : IsCompact (stdSimplex ℝ (Fin (d+1)) ×ˢ Set.pi univ (fun _ : Fin (d+1) => s)) :=
    (isCompact_stdSimplex ℝ _).prod (isCompact_univ_pi (fun _ => hs))
  suffices h : convexHull ℝ s = Φ '' (stdSimplex ℝ (Fin (d+1)) ×ˢ Set.pi univ (fun _ : Fin (d+1) => s)) by
    rw [h]; exact hD.image hΦ
  apply Subset.antisymm
  · intro x hx
    rw [convexHull_eq_union] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨t, hts, hai, hxt⟩ := hx
    have hcard : Fintype.card t ≤ Fintype.card (Fin (d+1)) := by
      have h1 := hai.card_le_finrank_succ
      have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ d :=
        Submodule.finrank_le _
      simp only [Fintype.card_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let e' : E → Fin (d+1) := fun y => if h : y ∈ t then e ⟨y, h⟩ else 0
    have he' : InjOn e' t := by
      intro a ha b hb hab
      have ha' : a ∈ t := ha
      have hb' : b ∈ t := hb
      simp only [e', dif_pos ha', dif_pos hb'] at hab
      exact congrArg Subtype.val (e.injective hab)
    rw [Finset.mem_convexHull'] at hxt
    obtain ⟨w, hw0, hw1, hwx⟩ := hxt
    let P : Fin (d+1) → E := fun j => if j ∈ e' '' t then Function.invFunOn e' t j else y₀
    let W : Fin (d+1) → ℝ := fun j => if j ∈ e' '' t then w (Function.invFunOn e' t j) else 0
    have hinv : ∀ y ∈ t, Function.invFunOn e' t (e' y) = y := fun y hy =>
      he'.leftInvOn_invFunOn (by exact hy)
    have hmemim : ∀ y ∈ t, e' y ∈ e' '' (t : Set E) := fun y hy => mem_image_of_mem e' hy
    refine ⟨(W, P), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro j
      simp only [W]
      split_ifs with hj
      · exact hw0 _ (Function.invFunOn_mem hj)
      · exact le_rfl
    · rw [← hw1]; symm
      apply Finset.sum_of_injOn e' he' (by intro a _; simp)
      · intro j _ hj; simp only [W, if_neg hj]
      · intro y hy; simp only [W, if_pos (hmemim y hy), hinv y hy]
    · intro j _
      simp only [P]
      split_ifs with hj
      · exact hts (Function.invFunOn_mem hj)
      · exact hy₀
    · show ∑ i, W i • P i = x
      rw [← hwx]; symm
      apply Finset.sum_of_injOn e' he' (by intro a _; simp)
      · intro j _ hj; simp only [W, if_neg hj, zero_smul]
      · intro y hy; simp only [W, P, if_pos (hmemim y hy), hinv y hy]
  · rintro _ ⟨⟨w, p⟩, ⟨⟨hw0, hw1⟩, hp⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw0 i) hw1
      (fun i _ => subset_convexHull ℝ s (hp i (mem_univ i)))

lemma aux_mgl_tend {X : Type*} [PseudoMetricSpace X] (a : ℕ → X) (b : X)
    (h : ∀ k, dist (a k) b < 1 / ((k:ℝ) + 1)) : Tendsto a atTop (𝓝 b) :=
  tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun k => dist_nonneg) (fun k => (h k).le) tendsto_one_div_add_atTop_nhds_zero_nat)

/-- Differentiation under the integral sign for averages of a Lipschitz function along a line. -/
lemma aux_mgl_hasDerivAt {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (B : Set (EuclideanSpace ℝ (Fin n))) (hB : Bornology.IsBounded B)
    (w : EuclideanSpace ℝ (Fin n)) (t₀ : ℝ) :
    Integrable (fun a => fderiv ℝ g (a + t₀ • w) w) (volume.restrict B) ∧
    HasDerivAt (fun t => ∫ a in B, g (a + t • w)) (∫ a in B, fderiv ℝ g (a + t₀ • w) w) t₀ := by
  have hfin : volume B < ⊤ := hB.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hfin.ne
  have hcont : ∀ t : ℝ, Continuous (fun a => g (a + t • w)) := fun t =>
    hg.continuous.comp (continuous_id.add continuous_const)
  refine hasDerivAt_integral_of_dominated_loc_of_lip (s := univ)
    (bound := fun _ => (K:ℝ) * ‖w‖) univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun t => (hcont t).aestronglyMeasurable)
  · exact ((hcont t₀).continuousOn.integrableOn_compact hB.isCompact_closure).mono_set subset_closure
  · exact ((measurable_fderiv_apply_const ℝ g w).comp
      (measurable_id.add_const _)).aestronglyMeasurable
  · refine Eventually.of_forall (fun a => ?_)
    refine LipschitzOnWith.of_dist_le_mul (fun s _ t _ => ?_)
    rw [Real.coe_nnabs]
    calc dist (g (a + s • w)) (g (a + t • w)) ≤ K * dist (a + s • w) (a + t • w) :=
          hg.dist_le_mul _ _
      _ = K * (|s - t| * ‖w‖) := by
          rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      _ = |(K:ℝ) * ‖w‖| * dist s t := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ K * ‖w‖), Real.dist_eq]; ring
  · exact integrable_const _
  · have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ g z :=
      hg.ae_differentiableAt
    have hae' : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ g (a + t₀ • w) :=
      (measurePreserving_add_right volume (t₀ • w)).quasiMeasurePreserving.ae hae
    refine ae_restrict_of_ae (hae'.mono fun a ha => ?_)
    have h1 : HasDerivAt (fun t : ℝ => a + t • w) w t₀ := by
      simpa using ((hasDerivAt_id t₀).smul_const w).const_add a
    exact ha.hasFDerivAt.comp_hasDerivAt t₀ h1

/-- A one-sided mean value inequality for a Lipschitz function whose derivative in direction `w`
is bounded above at all points of differentiability near `x`. -/
lemma aux_mgl_meanValue {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (x w : EuclideanSpace ℝ (Fin n)) (r C : ℝ)
    (hC : ∀ z, dist z x < r → DifferentiableAt ℝ g z → fderiv ℝ g z w ≤ C)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * ‖w‖ < r) : g (x + δ • w) - g x ≤ C * δ := by
  by_contra hlt
  push_neg at hlt
  set c := (g (x + δ • w) - g x - C * δ) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hF : Continuous (fun a => g (a + δ • w) - g a) :=
    (hg.continuous.comp (continuous_id.add continuous_const)).sub hg.continuous
  have hev : ∀ᶠ a in 𝓝 x, C * δ + c < g (a + δ • w) - g a := by
    have : C * δ + c < g (x + δ • w) - g x := by rw [hc]; linarith
    exact hF.continuousAt.eventually (lt_mem_nhds this)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set η := min ε (r - δ * ‖w‖) with hηdef
  have hη : 0 < η := lt_min hε (by linarith)
  set B := ball x η with hB
  set V := (volume : Measure (EuclideanSpace ℝ (Fin n))).real B with hV
  have hVpos : 0 < V := by
    rw [hV, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume x hη).ne' measure_ball_lt_top.ne
  let h : ℝ → ℝ := fun t => ∫ a in B, g (a + t • w)
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hderiv : ∀ t, Integrable (fun a => fderiv ℝ g (a + t • w) w) (volume.restrict B) ∧
      HasDerivAt h (∫ a in B, fderiv ℝ g (a + t • w) w) t := fun t =>
    aux_mgl_hasDerivAt g hg B isBounded_ball w t
  have hle : ∀ t ∈ interior (Icc 0 δ), deriv h t ≤ C * V := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t).2.deriv]
    have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ g z :=
      hg.ae_differentiableAt
    have hae' : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ g (a + t • w) :=
      (measurePreserving_add_right volume (t • w)).quasiMeasurePreserving.ae hae
    have hbd : (fun a => fderiv ℝ g (a + t • w) w) ≤ᵐ[volume.restrict B] (fun _ => C) := by
      rw [EventuallyLE, ae_restrict_iff' measurableSet_ball]
      refine hae'.mono fun a ha haB => ?_
      apply hC _ _ ha
      have haB' : dist a x < η := haB
      have h1 : dist (a + t • w) x ≤ dist a x + t * ‖w‖ := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
        calc ‖a - x + t • w‖ ≤ ‖a - x‖ + ‖t • w‖ := norm_add_le _ _
          _ = ‖a - x‖ + t * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      have h2 : t * ‖w‖ ≤ δ * ‖w‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
      have h3 : η ≤ r - δ * ‖w‖ := min_le_right _ _
      linarith
    calc ∫ a in B, fderiv ℝ g (a + t • w) w ≤ ∫ _ in B, C :=
          integral_mono_ae (hderiv t).1 (integrable_const C) hbd
      _ = C * V := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hmv := (convex_Icc (0:ℝ) δ).image_sub_le_mul_sub_of_deriv_le
    (fun t _ => ((hderiv t).2.continuousAt).continuousWithinAt)
    (fun t _ => ((hderiv t).2.differentiableAt).differentiableWithinAt) hle
    0 ⟨le_rfl, hδ0⟩ δ ⟨hδ0, le_rfl⟩ hδ0
  have hint : ∀ s : ℝ, IntegrableOn (fun a => g (a + s • w)) B volume := fun s =>
    ((hg.continuous.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_closedBall x η)).mono_set ball_subset_closedBall
  have hint0 : IntegrableOn (fun a => g a) B volume :=
    (hg.continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall x η)).mono_set ball_subset_closedBall
  have hdiff : h δ - h 0 = ∫ a in B, (g (a + δ • w) - g a) := by
    simp only [h, zero_smul, add_zero]
    rw [← integral_sub (hint δ) hint0]
  have hlow : (C * δ + c) * V ≤ ∫ a in B, (g (a + δ • w) - g a) := by
    apply setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne
    · intro a ha
      exact (hball a (ball_subset_ball (min_le_left _ _) ha)).le
    · exact (hint δ).sub hint0
  rw [hdiff] at hmv
  nlinarith

end ClarkeGradients.MaxFunctions

open ClarkeGradients.MaxFunctions
open Filter Topology

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ClarkeGradients.Shared.LipschitzOnBounded f) (x ζ : EuclideanSpace ℝ (Fin n))
    (h : ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ ζ v ≤ limsup (fun δ : ℝ => (f (x + δ • v) - f x) / δ) (𝓝[>] (0 : ℝ))) :
    ζ ∈ ClarkeGradients.Shared.generalizedGradient f x := by
  classical
  open Metric Set in
  obtain ⟨K, hK⟩ := hf (ball x 1) isBounded_ball
  obtain ⟨g, hgL, hfg⟩ := hK.extend_real
  have hloc : ∀ z ∈ Metric.ball x 1, f =ᶠ[𝓝 z] g := fun z hz =>
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) hfg
  let G : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun m =>
    {y | ∃ z, dist z x < 1 / ((m:ℝ) + 1) ∧ DifferentiableAt ℝ f z ∧ gradient f z = y}
  let T : Set (EuclideanSpace ℝ (Fin n)) := ⋂ m, closure (G m)
  have hgradbd : ∀ z ∈ Metric.ball x 1, DifferentiableAt ℝ f z → ‖gradient f z‖ ≤ K := by
    intro z hz _
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hz) hK
  have hTS : T ⊆ ClarkeGradients.Shared.gradientLimits f x := by
    intro ξ hξ
    have hm : ∀ m : ℕ, ∃ z, dist z x < 1 / ((m:ℝ)+1) ∧ DifferentiableAt ℝ f z ∧
        dist (gradient f z) ξ < 1 / ((m:ℝ)+1) := by
      intro m
      have := Set.mem_iInter.1 hξ m
      obtain ⟨y, ⟨z, hz, hd, rfl⟩, hy⟩ :=
        Metric.mem_closure_iff.1 this (1 / ((m:ℝ)+1)) Nat.one_div_pos_of_nat
      exact ⟨z, hz, hd, by rw [dist_comm]; exact hy⟩
    choose z hz using hm
    refine ⟨fun k => z k - x, ?_, ?_, ?_⟩
    · have : Tendsto z atTop (𝓝 x) := aux_mgl_tend z x (fun k => (hz k).1)
      simpa using this.sub_const x
    · intro i; simpa using (hz i).2.1
    · simpa using aux_mgl_tend (fun k => gradient f (z k)) ξ (fun k => (hz k).2.2)
  have hTclosed : IsClosed T := isClosed_iInter fun m => isClosed_closure
  have hTbdd : T ⊆ Metric.closedBall 0 K := by
    intro ξ hξ
    have h0 : ξ ∈ closure (G 0) := Set.mem_iInter.1 hξ 0
    refine closure_minimal ?_ Metric.isClosed_closedBall h0
    rintro _ ⟨z, hz, hd, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hgradbd z (by simpa using hz) hd
  have hTc : IsCompact T := (isCompact_closedBall 0 (K:ℝ)).of_isClosed_subset hTclosed hTbdd
  have hconvc : IsCompact (convexHull ℝ T) := aux_mgl_isCompact_convexHull hTc
  apply convexHull_mono hTS
  by_contra hζ
  obtain ⟨ℓ, u, hℓT, hℓζ⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ T) hconvc.isClosed hζ
  set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ℓ with hw
  have hℓw : ∀ y, ℓ y = inner ℝ w y := fun y => (InnerProductSpace.toDual_symm_apply).symm
  have hfd : ∀ z, fderiv ℝ f z w = ℓ (gradient f z) := by
    intro z
    rw [hℓw, real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  have hclaim : ∃ r > 0, ∀ z, dist z x < r → DifferentiableAt ℝ f z → fderiv ℝ f z w ≤ u := by
    by_contra hne
    push_neg at hne
    choose z hz using fun k : ℕ => hne (1 / ((k:ℝ) + 1)) Nat.one_div_pos_of_nat
    have hzt : Tendsto z atTop (𝓝 x) := aux_mgl_tend z x (fun k => (hz k).1)
    have hz1 : ∀ k, z k ∈ Metric.ball x 1 := by
      intro k
      have h1 : 1 / ((k:ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0:ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      exact lt_of_lt_of_le (hz k).1 h1
    have hyb : ∀ k, gradient f (z k) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) K :=
      fun k => mem_closedBall_zero_iff.2 (hgradbd _ (hz1 k) (hz k).2.1)
    obtain ⟨ξ, -, φ, hφ, hξ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hyb
    have hξT : ξ ∈ T := by
      refine Set.mem_iInter.2 fun m => mem_closure_of_tendsto hξ ?_
      have : ∀ᶠ k in atTop, z (φ k) ∈ Metric.ball x (1 / ((m:ℝ)+1)) :=
        (hzt.comp hφ.tendsto_atTop).eventually (Metric.ball_mem_nhds x Nat.one_div_pos_of_nat)
      exact this.mono fun k hk => ⟨z (φ k), hk, (hz _).2.1, rfl⟩
    have hξu : u ≤ ℓ ξ := by
      have : Tendsto (fun k => ℓ (gradient f (z (φ k)))) atTop (𝓝 (ℓ ξ)) :=
        (ℓ.continuous.tendsto ξ).comp hξ
      exact ge_of_tendsto' this fun k => by rw [← hfd]; exact (hz _).2.2.le
    have := hℓT ξ (subset_convexHull ℝ T hξT)
    linarith
  obtain ⟨r, hr, hrC⟩ := hclaim
  set r' := min r 1 with hr'
  have hr'pos : 0 < r' := lt_min hr one_pos
  have hgC : ∀ z, dist z x < r' → DifferentiableAt ℝ g z → fderiv ℝ g z w ≤ u := by
    intro z hz hd
    have hz1 : z ∈ Metric.ball x 1 := lt_of_lt_of_le hz (min_le_right _ _)
    have heq := hloc z hz1
    rw [← heq.fderiv_eq]
    exact hrC z (lt_of_lt_of_le hz (min_le_left _ _)) (heq.differentiableAt_iff.2 hd)
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), -((K:ℝ) * ‖w‖) ≤ (f (x + δ • w) - f x) / δ ∧
      (f (x + δ • w) - f x) / δ ≤ u := by
    have hpos : 0 < r' / (‖w‖ + 1) := div_pos hr'pos (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    have hδw : δ * ‖w‖ < r' := by
      rw [lt_div_iff₀ (by positivity)] at hδ1
      nlinarith [norm_nonneg w]
    have hmv := aux_mgl_meanValue g hgL x w r' u hgC δ hδ0.le hδw
    have hx1 : x + δ • w ∈ Metric.ball x 1 := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδ0.le]
      exact lt_of_lt_of_le hδw (min_le_right _ _)
    have hx0 : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
    rw [hfg hx1, hfg hx0]
    have hlip : |g (x + δ • w) - g x| ≤ K * (δ * ‖w‖) := by
      have := hgL.dist_le_mul (x + δ • w) x
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδ0.le] at this
      exact this
    constructor
    · rw [le_div_iff₀ hδ0]
      have := neg_abs_le (g (x + δ • w) - g x)
      nlinarith
    · rw [div_le_iff₀ hδ0]; linarith
  have hls : limsup (fun δ : ℝ => (f (x + δ • w) - f x) / δ) (𝓝[>] 0) ≤ u := by
    refine limsup_le_of_le ?_ (hev.mono fun δ hδ => hδ.2)
    exact isCoboundedUnder_le_of_eventually_le _ (hev.mono fun δ hδ => hδ.1)
  have h1 := h w
  have h2 : inner ℝ ζ w = ℓ ζ := by rw [hℓw, real_inner_comm]
  linarith
