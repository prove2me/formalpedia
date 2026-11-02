-- Prove2me | solution 1 for EthierKurtz.oblique_boundary_datum_c1_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T05:50:19.776374+00:00
-- url     : https://prove2.me/submissions/79d3a6d5-5872-44fa-9152-3efff8faa58f

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace P50e4

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- differentiability of the boundary datum `z ↦ ζ (X z) * DG (X z) (C z)` -/
lemma qdiff (G : Y → ℝ) (hG : ContDiff ℝ 2 G) (ζ : Y → ℝ) (hζ : ContDiff ℝ 1 ζ)
    (X : E → Y) (C : E → Y) (z : E) (hX : DifferentiableAt ℝ X z)
    (hC : DifferentiableAt ℝ C z) :
    DifferentiableAt ℝ (fun z => ζ (X z) * fderiv ℝ G (X z) (C z)) z := by
  have hG1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  exact (((hζ.differentiable one_ne_zero) (X z)).comp z hX).mul
    ((((hG1.differentiable one_ne_zero) (X z)).comp z hX).clm_apply hC)

/-- derivative bound for the boundary datum `z ↦ ζ (X z) * DG (X z) (C z)` -/
lemma qderiv_bound (G : Y → ℝ) (hG : ContDiff ℝ 2 G) (ζ : Y → ℝ) (hζ : ContDiff ℝ 1 ζ)
    (X : E → Y) (C : E → Y) (z : E) (hX : DifferentiableAt ℝ X z)
    (hC : DifferentiableAt ℝ C z)
    {a b Mζ Mζ' MX Mc Mc' : ℝ} (ha : ‖fderiv ℝ G (X z)‖ ≤ a)
    (hb : ‖fderiv ℝ (fderiv ℝ G) (X z)‖ ≤ b)
    (hMζ : |ζ (X z)| ≤ Mζ) (hMζ' : ‖fderiv ℝ (fun z => ζ (X z)) z‖ ≤ Mζ')
    (hMX : ‖fderiv ℝ X z‖ ≤ MX) (hMc : ‖C z‖ ≤ Mc) (hMc' : ‖fderiv ℝ C z‖ ≤ Mc')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    ‖fderiv ℝ (fun z => ζ (X z) * fderiv ℝ G (X z) (C z)) z‖ ≤
      Mζ * (a * Mc' + b * MX * Mc) + a * Mc * Mζ' := by
  have hG1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hA : HasFDerivAt (fun z => fderiv ℝ G (X z))
      ((fderiv ℝ (fderiv ℝ G) (X z)).comp (fderiv ℝ X z)) z :=
    ((hG1.differentiable one_ne_zero) (X z)).hasFDerivAt.comp z hX.hasFDerivAt
  have hAC := hA.clm_apply hC.hasFDerivAt
  have hZ : HasFDerivAt (fun z => ζ (X z)) (fderiv ℝ (fun z => ζ (X z)) z) z :=
    (((hζ.differentiable one_ne_zero) (X z)).comp z hX).hasFDerivAt
  have hQ : HasFDerivAt (fun z => ζ (X z) * fderiv ℝ G (X z) (C z)) _ z := hZ.mul hAC
  rw [hQ.fderiv]
  have hMζ0 : 0 ≤ Mζ := (abs_nonneg _).trans hMζ
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans hMc
  have hMX0 : 0 ≤ MX := (norm_nonneg _).trans hMX
  have hL : ‖(fderiv ℝ G (X z)).comp (fderiv ℝ C z) +
      ((fderiv ℝ (fderiv ℝ G) (X z)).comp (fderiv ℝ X z)).flip (C z)‖ ≤
        a * Mc' + b * MX * Mc := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul ha hMc' (norm_nonneg _) ha0)
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hb hMX (norm_nonneg _) hb0)) hMc (norm_nonneg _) (mul_nonneg hb0 hMX0)
  have hv : |fderiv ℝ G (X z) (C z)| ≤ a * Mc := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ G (X z)).le_opNorm _).trans (mul_le_mul ha hMc (norm_nonneg _) ha0)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have k1 := mul_le_mul hMζ hL (norm_nonneg _) hMζ0
  have k2 := mul_le_mul hv hMζ' (norm_nonneg _) (mul_nonneg ha0 hMc0)
  linarith

/-- E4: if `F k` approximates (in `C²` on `Ω`) a function whose derivative extends to `J` on
`closure Ω` with `J(c) = 0` on the frontier, then the oblique boundary datum of `F k` along a
boundary parametrisation `X` tends to `0` in `C¹`. -/
theorem boundary_datum_vanishing [ProperSpace E] {Ω : Set Y} (c : Y → Y)
    (J : Y → (Y →L[ℝ] ℝ))
    (hJ : ContinuousOn J (closure Ω)) (hJc : ∀ y ∈ frontier Ω, J y (c y) = 0)
    (X : E → Y) (O : Set E) (hO : IsOpen O) (r : ℝ) (hr0 : 0 < r)
    (hr : Metric.closedBall 0 r ⊆ O) (hX : ContDiffOn ℝ 1 X O)
    (hcX : ContDiffOn ℝ 1 (fun z => c (X z)) O) (hXf : ∀ z ∈ O, X z ∈ frontier Ω)
    (ζ : Y → ℝ) (hζ : ContDiff ℝ 1 ζ)
    (F : ℕ → Y → ℝ) (hF : ∀ k, ContDiff ℝ 2 (F k)) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (h1 : ∀ k, ∀ y ∈ Ω, ‖fderiv ℝ (F k) y - J y‖ ≤ η k)
    (h2 : ∀ k l, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ (F k)) y - fderiv ℝ (fderiv ℝ (F l)) y‖ ≤ η k + η l) :
    ∀ δ > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ z ∈ Metric.closedBall (0 : E) r,
      |ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))| ≤ δ ∧
      ‖fderiv ℝ (fun z => ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))) z‖ ≤ δ := by
  obtain ⟨δ0, hδ0, hthick⟩ :=
    (isCompact_closedBall (0 : E) r).exists_cthickening_subset_open hO hr
  rw [cthickening_closedBall hδ0.le hr0.le] at hthick
  set r' := δ0 + r with hr'
  have hB : Metric.closedBall (0 : E) r' ⊆ O := hthick
  have hrs : Metric.closedBall (0 : E) r ⊆ Metric.ball 0 r' :=
    Metric.closedBall_subset_ball (by linarith)
  have hsO : Metric.ball (0 : E) r' ⊆ O := Metric.ball_subset_closedBall.trans hB
  have hK : IsCompact (Metric.closedBall (0 : E) r') := isCompact_closedBall _ _
  have h0B : (0 : E) ∈ Metric.closedBall (0 : E) r' :=
    Metric.mem_closedBall_self (by linarith)
  -- closure extensions
  have hcl : ∀ z ∈ O, X z ∈ closure Ω := fun z hz => frontier_subset_closure (hXf z hz)
  have e1 : ∀ k, ∀ y ∈ closure Ω, ‖fderiv ℝ (F k) y - J y‖ ≤ η k := by
    intro k y hy
    haveI := mem_closure_iff_nhdsWithin_neBot.mp hy
    have hc : ContinuousWithinAt (fun w => ‖fderiv ℝ (F k) w - J w‖) Ω y :=
      ((((hF k).continuous_fderiv (by norm_num)).continuousAt).continuousWithinAt.sub
        ((hJ y hy).mono subset_closure)).norm
    exact le_of_tendsto hc (eventually_nhdsWithin_of_forall fun w hw => h1 k w hw)
  have hd2 : ∀ k, Continuous (fderiv ℝ (fderiv ℝ (F k))) := fun k =>
    ((hF k).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have e2 : ∀ k l, ∀ y ∈ closure Ω,
      ‖fderiv ℝ (fderiv ℝ (F k)) y - fderiv ℝ (fderiv ℝ (F l)) y‖ ≤ η k + η l := by
    intro k l y hy
    haveI := mem_closure_iff_nhdsWithin_neBot.mp hy
    have hcont : Continuous (fun w => fderiv ℝ (fderiv ℝ (F k)) w - fderiv ℝ (fderiv ℝ (F l)) w) :=
      (hd2 k).sub (hd2 l)
    have hmem := (Metric.isClosed_closedBall (x := (0 : Y →L[ℝ] Y →L[ℝ] ℝ))
      (ε := η k + η l)).mem_of_tendsto
      ((hcont.continuousAt (x := y)).tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun w hw =>
        (mem_closedBall_zero_iff (E := Y →L[ℝ] Y →L[ℝ] ℝ)).mpr (h2 k l w hw))
    exact (mem_closedBall_zero_iff (E := Y →L[ℝ] Y →L[ℝ] ℝ)).mp hmem
  have hη0 : ∀ k, 0 ≤ η k := fun k =>
    (norm_nonneg _).trans (e1 k (X 0) (hcl 0 (hB h0B)))
  -- bounds on the compact ball
  have hXc : ContinuousOn (fderiv ℝ X) O := hX.continuousOn_fderiv_of_isOpen hO le_rfl
  have hCc : ContinuousOn (fderiv ℝ (fun z => c (X z))) O :=
    hcX.continuousOn_fderiv_of_isOpen hO le_rfl
  have hζX : ContDiffOn ℝ 1 (fun z => ζ (X z)) O := hζ.comp_contDiffOn hX
  have hζc : ContinuousOn (fderiv ℝ (fun z => ζ (X z))) O :=
    hζX.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨MX, hMX⟩ := hK.exists_bound_of_continuousOn (hXc.mono hB)
  obtain ⟨Mc', hMc'⟩ := hK.exists_bound_of_continuousOn (hCc.mono hB)
  obtain ⟨Mζ', hMζ'⟩ := hK.exists_bound_of_continuousOn (hζc.mono hB)
  obtain ⟨Mc, hMc⟩ := hK.exists_bound_of_continuousOn (hcX.continuousOn.mono hB)
  obtain ⟨Mζ, hMζ⟩ := hK.exists_bound_of_continuousOn (hζX.continuousOn.mono hB)
  have hMX0 : 0 ≤ MX := (norm_nonneg _).trans (hMX 0 h0B)
  have hMc'0 : 0 ≤ Mc' := (norm_nonneg _).trans (hMc' 0 h0B)
  have hMζ'0 : 0 ≤ Mζ' := (norm_nonneg _).trans (hMζ' 0 h0B)
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc 0 h0B)
  have hMζ0 : 0 ≤ Mζ := (norm_nonneg _).trans (hMζ 0 h0B)
  have hXd : ∀ z ∈ Metric.ball (0 : E) r', DifferentiableAt ℝ X z := fun z hz =>
    (hX.contDiffAt (hO.mem_nhds (hsO hz))).differentiableAt one_ne_zero
  have hCd : ∀ z ∈ Metric.ball (0 : E) r', DifferentiableAt ℝ (fun z => c (X z)) z :=
    fun z hz => (hcX.contDiffAt (hO.mem_nhds (hsO hz))).differentiableAt one_ne_zero
  -- the data
  set Q : ℕ → E → ℝ := fun k z => ζ (X z) * fderiv ℝ (F k) (X z) (c (X z)) with hQdef
  have hQd : ∀ k, ∀ z ∈ Metric.ball (0 : E) r', DifferentiableAt ℝ (Q k) z := fun k z hz =>
    qdiff (F k) (hF k) ζ hζ X (fun z => c (X z)) z (hXd z hz) (hCd z hz)
  have hQ0 : ∀ k, ∀ z ∈ Metric.ball (0 : E) r', |Q k z| ≤ Mζ * (η k * Mc) := by
    intro k z hz
    have hzB := Metric.ball_subset_closedBall hz
    have hJ0 := hJc (X z) (hXf z (hsO hz))
    have e : Q k z = ζ (X z) * (fderiv ℝ (F k) (X z) - J (X z)) (c (X z)) := by
      simp only [hQdef, ContinuousLinearMap.sub_apply, hJ0, sub_zero]
    rw [e, abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) hMζ0
    · rw [← Real.norm_eq_abs]; exact hMζ z hzB
    · rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (F k) (X z) - J (X z)).le_opNorm _).trans
        (mul_le_mul (e1 k _ (hcl z (hsO hz))) (hMc z hzB) (norm_nonneg _) (hη0 k))
  -- Cauchy estimate for the derivatives
  set Cst : ℝ := Mζ * (Mc' + MX * Mc) + Mc * Mζ' with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  have hDiff : ∀ k l, ∀ z ∈ Metric.ball (0 : E) r',
      ‖fderiv ℝ (Q k) z - fderiv ℝ (Q l) z‖ ≤ Cst * (η k + η l) := by
    intro k l z hz
    have hzB := Metric.ball_subset_closedBall hz
    set G : Y → ℝ := fun y => F k y - F l y with hGdef
    have hG : ContDiff ℝ 2 G := (hF k).sub (hF l)
    have hDG : fderiv ℝ G = fun y => fderiv ℝ (F k) y - fderiv ℝ (F l) y := by
      funext y
      exact fderiv_sub (((hF k).differentiable (by norm_num)) y)
        (((hF l).differentiable (by norm_num)) y)
    have hD2G : ∀ y, fderiv ℝ (fderiv ℝ G) y =
        fderiv ℝ (fderiv ℝ (F k)) y - fderiv ℝ (fderiv ℝ (F l)) y := by
      intro y
      rw [hDG]
      exact fderiv_sub ((((hF k).fderiv_right (m := 1) (by norm_num)).differentiable
        one_ne_zero) y) ((((hF l).fderiv_right (m := 1) (by norm_num)).differentiable
          one_ne_zero) y)
    have hQe : Q k - Q l = fun z => ζ (X z) * fderiv ℝ G (X z) (c (X z)) := by
      funext w
      simp only [Pi.sub_apply, hQdef, hDG, ContinuousLinearMap.sub_apply]
      ring
    rw [← fderiv_sub (hQd k z hz) (hQd l z hz), hQe]
    have hxc := hcl z (hsO hz)
    have ha : ‖fderiv ℝ G (X z)‖ ≤ η k + η l := by
      rw [hDG]
      refine (norm_sub_le_norm_sub_add_norm_sub _ (J (X z)) _).trans ?_
      rw [norm_sub_rev (J (X z))]
      exact add_le_add (e1 k _ hxc) (e1 l _ hxc)
    have hb : ‖fderiv ℝ (fderiv ℝ G) (X z)‖ ≤ η k + η l := by
      rw [hD2G]; exact e2 k l _ hxc
    refine (qderiv_bound G hG ζ hζ X (fun z => c (X z)) z (hXd z hz) (hCd z hz) ha hb
      ((Real.norm_eq_abs _).symm.le.trans (hMζ z hzB)) (hMζ' z hzB) (hMX z hzB) (hMc z hzB)
      (hMc' z hzB) (add_nonneg (hη0 k) (hη0 l)) (add_nonneg (hη0 k) (hη0 l))).trans ?_
    exact le_of_eq (by rw [hCst]; ring)
  -- uniform Cauchy, uniform limit, and the limit is the derivative of `0`
  have hηsmall : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, η k < ε := by
    intro ε hε
    exact eventually_atTop.mp (hη.eventually (gt_mem_nhds hε))
  have hcauchy : UniformCauchySeqOn (fun k => fderiv ℝ (Q k)) atTop (Metric.ball (0 : E) r') := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set ε' : ℝ := ε / (2 * Cst + 1) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hε'e : ε' * (2 * Cst + 1) = ε := div_mul_cancel₀ _ (by positivity)
    obtain ⟨N, hN⟩ := hηsmall ε' hε'0
    refine ⟨N, fun k hk l hl z hz => ?_⟩
    rw [dist_eq_norm]
    have h3 := hDiff k l z hz
    have h4 : Cst * (η k + η l) ≤ Cst * (2 * ε') :=
      mul_le_mul_of_nonneg_left (by linarith [hN k hk, hN l hl]) hCst0
    nlinarith
  have hlim : ∀ z ∈ Metric.ball (0 : E) r', Tendsto (fun k => fderiv ℝ (Q k) z) atTop
      (𝓝 (limUnder atTop (fun k => fderiv ℝ (Q k) z))) := fun z hz =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hz))
  have hunif := hcauchy.tendstoUniformlyOn_of_tendsto hlim
  have hQlim : ∀ z ∈ Metric.ball (0 : E) r', Tendsto (fun k => Q k z) atTop (𝓝 0) := by
    intro z hz
    refine squeeze_zero_norm (fun k => (Real.norm_eq_abs _).le.trans (hQ0 k z hz)) ?_
    have := (hη.mul_const Mc).const_mul Mζ
    simpa using this
  have hzero : ∀ z ∈ Metric.ball (0 : E) r', limUnder atTop (fun k => fderiv ℝ (Q k) z) = 0 := by
    intro z hz
    have hfd := hasFDerivAt_of_tendstoUniformlyOn (g := fun _ : E => (0 : ℝ)) Metric.isOpen_ball
      hunif (fun k x hx => (hQd k x hx).hasFDerivAt) hQlim hz
    exact hfd.unique (hasFDerivAt_const 0 z)
  have hunif0 : TendstoUniformlyOn (fun k => fderiv ℝ (Q k)) (fun _ => 0) atTop
      (Metric.ball (0 : E) r') := hunif.congr_right fun z hz => hzero z hz
  -- conclusion
  intro δ hδ
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunif0) δ hδ)
  set δ' : ℝ := δ / (Mζ * Mc + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'e : δ' * (Mζ * Mc + 1) = δ := div_mul_cancel₀ _ (by positivity)
  obtain ⟨N2, hN2⟩ := hηsmall δ' hδ'0
  refine ⟨max N1 N2, fun k hk z hz => ⟨?_, ?_⟩⟩
  · have h5 := hQ0 k z (hrs hz)
    have h6 := hN2 k (le_of_max_le_right hk)
    have h7 : Mζ * (η k * Mc) ≤ Mζ * (δ' * Mc) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6.le hMc0) hMζ0
    nlinarith [mul_nonneg hMζ0 hMc0]
  · have h8 := hN1 k (le_of_max_le_left hk) z (hrs hz)
    rw [dist_eq_norm, zero_sub, norm_neg] at h8
    exact h8.le

end P50e4

open Filter Topology in
theorem solution (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (J : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hJ : ContinuousOn J (closure Ω)) (hJc : ∀ y ∈ frontier Ω, J y (c y) = 0)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)))
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (r : ℝ) (hr0 : 0 < r)
    (hr : Metric.closedBall 0 r ⊆ O) (hX : ContDiffOn ℝ 1 X O)
    (hcX : ContDiffOn ℝ 1 (fun z => c (X z)) O) (hXf : ∀ z ∈ O, X z ∈ frontier Ω)
    (ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hζ : ContDiff ℝ 1 ζ)
    (F : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ∀ k, ContDiff ℝ 2 (F k)) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (h1 : ∀ k, ∀ y ∈ Ω, ‖fderiv ℝ (F k) y - J y‖ ≤ η k)
    (h2 : ∀ k l, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ (F k)) y - fderiv ℝ (fderiv ℝ (F l)) y‖ ≤ η k + η l) :
    ∀ δ > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      |ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))| ≤ δ ∧
      ‖fderiv ℝ (fun z => ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))) z‖ ≤ δ := by
  exact P50e4.boundary_datum_vanishing c J hJ hJc X O hO r hr0 hr hX hcX hXf ζ hζ F hF η hη h1 h2
