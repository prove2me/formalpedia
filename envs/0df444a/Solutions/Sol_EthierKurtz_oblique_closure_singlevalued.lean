-- Prove2me | solution 1 for EthierKurtz.oblique_closure_singlevalued
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T07:36:35.80795+00:00
-- url     : https://prove2.me/submissions/43b92535-21d1-40e8-962a-15cafecbb01d

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace P74866daf

/-- One-dimensional second-order necessary condition at a local maximum. -/
lemma second_deriv_nonpos_of_localMax {h h' : ℝ → ℝ} {k : ℝ}
    (hmax : IsLocalMax h 0) (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt h (h' t) t)
    (h0 : h' 0 = 0) (hk : HasDerivAt h' k 0) : k ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hslope := hk.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t⁻¹ • (h' (0 + t) - h' 0) :=
    hslope.eventually (lt_mem_nhds hpos)
  have hall : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < h' t ∧ HasDerivAt h (h' t) t ∧ h t ≤ h 0 := by
    filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds hd,
      nhdsWithin_le_nhds hmax] with t ht htpos hdt hmt
    refine ⟨?_, hdt, hmt⟩
    simp only [zero_add, h0, sub_zero, smul_eq_mul] at ht
    have htp : (0:ℝ) < t := htpos
    have := mul_pos htp ht
    rwa [← mul_assoc, mul_inv_cancel₀ htp.ne', one_mul] at this
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  have hu0 : (0:ℝ) < u := hu
  set t : ℝ := u / 2 with ht
  have ht0 : 0 < t := by positivity
  have htu : t < u := by linarith
  have hP : ∀ s ∈ Set.Ioc 0 t, 0 < h' s ∧ HasDerivAt h (h' s) s ∧ h s ≤ h 0 :=
    fun s hs => hsub ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩
  have hcont : ContinuousOn h (Set.Icc 0 t) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · subst h1
      exact hd.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hP s ⟨h1, hs.2⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope h h' ht0 hcont
    (fun s hs => (hP s ⟨hs.1, hs.2.le⟩).2.1)
  have hpc := (hP c ⟨hc.1, hc.2.le⟩).1
  have hht := (hP t ⟨ht0, le_rfl⟩).2.2
  rw [hceq, sub_zero] at hpc
  have : 0 < h t - h 0 := by
    have := mul_pos hpc ht0
    rwa [div_mul_cancel₀ _ ht0.ne'] at this
  linarith

/-- Second-order necessary condition in a normed space. -/
lemma hess_nonpos_of_localMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) {x : E}
    (hx : x ∈ U) (hmax : IsLocalMax u x) (v : E) :
    fderiv ℝ (fderiv ℝ u) x v v ≤ 0 := by
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ u y := fun y hy =>
    (hu.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have hDu : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) U :=
    hu.fderiv_of_isOpen hU (by norm_num)
  have hDdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hDu.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hγ0 : (fun t : ℝ => x + t • v) 0 = x := by simp
  have hγd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    have := hc.tendsto 0
    simpa using this
  have hevU : ∀ᶠ t in 𝓝 (0:ℝ), x + t • v ∈ U := htend.eventually (hU.mem_nhds hx)
  apply second_deriv_nonpos_of_localMax (h := fun t => u (x + t • v))
    (h' := fun t => fderiv ℝ u (x + t • v) v)
  · have : ∀ᶠ t in 𝓝 (0:ℝ), u (x + t • v) ≤ u x := htend.eventually hmax
    show ∀ᶠ t in 𝓝 (0:ℝ), u (x + t • v) ≤ u (x + (0:ℝ) • v)
    simpa using this
  · filter_upwards [hevU] with t ht
    exact (hdiff _ ht).hasFDerivAt.comp_hasDerivAt t (hγd t)
  · simp [hmax.fderiv_eq_zero]
  · have h1 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x)
        ((fun t : ℝ => x + t • v) 0) := by rw [hγ0]; exact hDdiff.hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0:ℝ) (hγd 0)
    have h3 := h2.clm_apply (hasDerivAt_const (0:ℝ) v)
    simpa using h3

/-- PSD coefficient matrix against a nonpositive bilinear form. -/
lemma psd_sum_nonpos {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hB : ∀ v, B v v ≤ 0) :
    ∑ i, ∑ j, A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ 0 := by
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have hrow : ∀ k, B (∑ i, w k i • EuclideanSpace.single i (1:ℝ))
      (∑ j, w k j • EuclideanSpace.single j (1:ℝ)) = ∑ i, ∑ j,
        w k i * w k j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro k
    simp [map_sum, map_smul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have key : ∑ i, ∑ j, A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      = ∑ k, B (∑ i, w k i • EuclideanSpace.single i (1:ℝ))
          (∑ j, w k j • EuclideanSpace.single j (1:ℝ)) := by
    simp only [hrow]
    subst hw
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial, Finset.sum_mul]
    calc _ = ∑ i, ∑ k, ∑ j, w k i * w k j *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [key]
  exact Finset.sum_nonpos (fun k _ => hB _)


/-- The interior operator of (1.15), exactly as in `obliqueDiffusionGraph`. -/
noncomputable def Lop {d : ℕ} (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
    a x i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)) + fderiv ℝ u x (b x)

lemma partial2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {x : E}
    (hD : DifferentiableAt ℝ (fderiv ℝ u) x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = fderiv ℝ (fderiv ℝ u) x v w := by
  rw [fderiv_clm_apply hD (differentiableAt_const w)]
  simp

/-- Interior positive maximum principle for the operator. -/
lemma max_principle {d : ℕ} {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U)
    (hmax : IsLocalMax u x) (ha : (a x).PosSemidef) : Lop a b u x ≤ 0 := by
  have hDu : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hDdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hDu.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hs := psd_sum_nonpos (a x) ha (fderiv ℝ (fderiv ℝ u) x)
    (fun v => hess_nonpos_of_localMax hU hu hx hmax v)
  unfold Lop
  simp only [partial2_eq hDdiff]
  rw [hmax.fderiv_eq_zero]
  simp only [ContinuousLinearMap.zero_apply, add_zero]
  linarith

/-- Linearity of the operator on functions that are `C²` on an open set. -/
lemma Lop_lin {d : ℕ} {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) (hG : ContDiffOn ℝ 2 G U)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) (c₁ c₂ : ℝ) :
    Lop a b (fun y => c₁ * F y + c₂ * G y) x = c₁ * Lop a b F x + c₂ * Lop a b G x := by
  have dF : ∀ y ∈ U, DifferentiableAt ℝ F y := fun y hy =>
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have dG : ∀ y ∈ U, DifferentiableAt ℝ G y := fun y hy =>
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have DF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hx)
  have DG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hx)
  have h1 : ∀ y ∈ U, fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y
      = c₁ • fderiv ℝ F y + c₂ • fderiv ℝ G y := by
    intro y hy
    rw [fderiv_fun_add ((dF y hy).const_mul c₁) ((dG y hy).const_mul c₂),
      fderiv_const_mul (dF y hy), fderiv_const_mul (dG y hy)]
  have h2 : ∀ j : Fin d, fderiv ℝ (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y
      (EuclideanSpace.single j 1)) x
      = c₁ • fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
        + c₂ • fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x := by
    intro j
    have hev : (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y (EuclideanSpace.single j 1))
        =ᶠ[𝓝 x] (fun y => c₁ * fderiv ℝ F y (EuclideanSpace.single j 1)
          + c₂ * fderiv ℝ G y (EuclideanSpace.single j 1)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [h1 y hy]
      simp
    rw [hev.fderiv_eq]
    have dFj : DifferentiableAt ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x :=
      DF.clm_apply (differentiableAt_const _)
    have dGj : DifferentiableAt ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x :=
      DG.clm_apply (differentiableAt_const _)
    rw [fderiv_fun_add (dFj.const_mul c₁) (dGj.const_mul c₂), fderiv_const_mul dFj,
      fderiv_const_mul dGj]
  unfold Lop
  simp only [h2, h1 x hx, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_left_comm _ c₁, mul_left_comm _ c₂,
    ← Finset.mul_sum]
  ring

lemma continuousOn_of_components {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : ∀ i, ContinuousOn (fun x => b x i) Ω) : ContinuousOn b Ω :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp_continuousOn
    (continuousOn_pi.mpr h)

lemma restr_eq {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (q : (closure Ω) →ᵇ ℝ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω) :
    EthierKurtz.closedRegionRestriction q y = q ⟨y, subset_closure hy⟩ := by
  unfold EthierKurtz.closedRegionRestriction
  rw [dif_pos (subset_closure hy)]

open EthierKurtz in
/-- Main pointwise inequality: two images of one function in the closed graph agree. -/
lemma closure_le {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ}
    {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haC : ∀ i j, ContinuousOn (fun x => a x i j) Ω) (hbC : ContinuousOn b Ω)
    {f g g' : (closure Ω) →ᵇ ℝ}
    (h : (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c))
    (h' : (f, g') ∈ closure (obliqueDiffusionGraph Ω μ a b c)) (z : closure Ω) :
    g z ≤ g' z := by
  by_contra hlt
  push Not at hlt
  set δ := g z - g' z with hδ
  have hδpos : 0 < δ := by linarith
  have hDc : Continuous (fun w : closure Ω => g w - g' w) := g.continuous.sub g'.continuous
  obtain ⟨r, hr, hrD⟩ := Metric.continuous_iff.mp hDc z (δ / 4) (by positivity)
  obtain ⟨x₁, hx₁Ω, hx₁z⟩ := Metric.mem_closure_iff.mp z.2 (r / 2) (by positivity)
  obtain ⟨ε₀, hε₀, hballΩ⟩ := Metric.isOpen_iff.mp hopen x₁ hx₁Ω
  set R := min ε₀ (r / 2) / 2 with hR
  have hRpos : 0 < R := by positivity
  have hRε : R < ε₀ := by
    have := min_le_left ε₀ (r / 2); rw [hR]; linarith
  have hRr : R ≤ r / 4 := by
    have := min_le_right ε₀ (r / 2); rw [hR]; linarith
  have hKΩ : Metric.closedBall x₁ R ⊆ Ω := fun y hy =>
    hballΩ (by rw [Metric.mem_ball]; exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) hRε)
  have hDK : ∀ y (hy : y ∈ Ω), dist y x₁ ≤ R →
      δ / 2 < g ⟨y, subset_closure hy⟩ - g' ⟨y, subset_closure hy⟩ := by
    intro y hy hyd
    have hdist : dist (⟨y, subset_closure hy⟩ : closure Ω) z < r := by
      rw [Subtype.dist_eq]
      have h1 : dist y (z : EuclideanSpace ℝ (Fin d)) ≤ dist y x₁ + dist x₁ z :=
        dist_triangle _ _ _
      have h2 : dist x₁ (z : EuclideanSpace ℝ (Fin d)) < r / 2 := by
        rw [dist_comm]; exact hx₁z
      linarith
    have := hrD _ hdist
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  -- the bump function
  let φ : ContDiffBump x₁ := ⟨R / 2, R, by positivity, by linarith⟩
  have hφ1 : φ x₁ = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
  have hφ0 : ∀ y, R ≤ dist y x₁ → φ y = 0 := fun y hy => φ.zero_of_le_dist hy
  have hφC : ContDiff ℝ 3 (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.contDiff
  have hφC2 : ContDiff ℝ 2 (φ : EuclideanSpace ℝ (Fin d) → ℝ) := φ.contDiff
  have hφD1 : Continuous (fun y => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) y) :=
    hφC.continuous_fderiv (by norm_num)
  have hφD2 : ∀ i j : Fin d, Continuous (fun y => fderiv ℝ (fun y =>
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) y (EuclideanSpace.single j 1)) y
        (EuclideanSpace.single i 1)) := by
    intro i j
    have h1 : ContDiff ℝ 2 (fun y => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) y) :=
      hφC.fderiv_right (m := 2) (by norm_num)
    have h2 : ContDiff ℝ 2 (fun y => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) y
        (EuclideanSpace.single j 1)) := h1.clm_apply contDiff_const
    exact (h2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hLφc : ContinuousOn (Lop a b (φ : EuclideanSpace ℝ (Fin d) → ℝ))
      (Metric.closedBall x₁ R) := by
    show ContinuousOn (fun x => (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
      a x i j * fderiv ℝ (fun y => fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1))
        + fderiv ℝ (φ : EuclideanSpace ℝ (Fin d) → ℝ) x (b x)) _
    refine ContinuousOn.add (continuousOn_const.mul ?_) (hφD1.continuousOn.clm_apply
      (hbC.mono hKΩ))
    refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
    exact ((haC i j).mono hKΩ).mul (hφD2 i j).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₁ R).exists_bound_of_continuousOn hLφc
  -- parameters
  set lam : ℝ := 4 * (|M| + 1) / δ with hlam
  have hlampos : 0 < lam := by positivity
  have hlamδ : lam * (δ / 4) = |M| + 1 := by
    rw [hlam]; field_simp
  set ε : ℝ := min (δ / 8) (1 / (8 * lam)) with hεdef
  have hε : 0 < ε := by positivity
  have hεδ : ε ≤ δ / 8 := min_le_left _ _
  have hεlam : lam * ε ≤ 1 / 8 := by
    have h1 : ε ≤ 1 / (8 * lam) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  -- approximants
  obtain ⟨p, hpG, hpd⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨p', hpG', hpd'⟩ := Metric.mem_closure_iff.mp h' ε hε
  rw [Prod.dist_eq] at hpd hpd'
  have hf1 : dist f p.1 < ε := lt_of_le_of_lt (le_max_left _ _) hpd
  have hg1 : dist g p.2 < ε := lt_of_le_of_lt (le_max_right _ _) hpd
  have hf2 : dist f p'.1 < ε := lt_of_le_of_lt (le_max_left _ _) hpd'
  have hg2 : dist g' p'.2 < ε := lt_of_le_of_lt (le_max_right _ _) hpd'
  obtain ⟨hC1, hL1, -⟩ := hpG
  obtain ⟨hC2, hL2, -⟩ := hpG'
  set F₁ := closedRegionRestriction p.1 with hF₁
  set F₂ := closedRegionRestriction p'.1 with hF₂
  have hpt : ∀ (q₁ q₂ : (closure Ω) →ᵇ ℝ) (w : closure Ω), dist q₁ q₂ < ε →
      |q₁ w - q₂ w| < ε := fun q₁ q₂ w hq => by
    rw [← Real.dist_eq]; exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist (f := q₁) (g := q₂) w) hq
  have hFF : ∀ y (hy : y ∈ Ω), |lam * F₁ y + (-lam) * F₂ y| ≤ 1 / 4 := by
    intro y hy
    rw [hF₁, hF₂, restr_eq _ hy, restr_eq _ hy]
    have e1 := abs_lt.mp (hpt _ _ ⟨y, subset_closure hy⟩ hf1)
    have e2 := abs_lt.mp (hpt _ _ ⟨y, subset_closure hy⟩ hf2)
    have hdiff : |p.1 ⟨y, subset_closure hy⟩ - p'.1 ⟨y, subset_closure hy⟩| ≤ 2 * ε := by
      rw [abs_le]; constructor <;> linarith
    have : lam * p.1 ⟨y, subset_closure hy⟩ + -lam * p'.1 ⟨y, subset_closure hy⟩
        = lam * (p.1 ⟨y, subset_closure hy⟩ - p'.1 ⟨y, subset_closure hy⟩) := by ring
    rw [this, abs_mul, abs_of_pos hlampos]
    nlinarith
  -- the test function
  set W : EuclideanSpace ℝ (Fin d) → ℝ := fun y => lam * F₁ y + (-lam) * F₂ y with hW
  have hWC : ContDiffOn ℝ 2 W Ω := (contDiffOn_const.mul hC1.1).add (contDiffOn_const.mul hC2.1)
  set u : EuclideanSpace ℝ (Fin d) → ℝ := fun y => 1 * W y + 1 * φ y with hu
  have huC : ContDiffOn ℝ 2 u Ω := (contDiffOn_const.mul hWC).add
    (contDiffOn_const.mul hφC2.contDiffOn)
  obtain ⟨xs, hxsK, hxsmax⟩ := (isCompact_closedBall x₁ R).exists_isMaxOn
    ⟨x₁, Metric.mem_closedBall_self hRpos.le⟩ (huC.continuousOn.mono hKΩ)
  have hxsΩ : xs ∈ Ω := hKΩ hxsK
  have hux₁ : 3 / 4 ≤ u x₁ := by
    have := abs_le.mp (hFF x₁ hx₁Ω)
    simp only [hu, hW, hφ1]; linarith
  have hxsball : dist xs x₁ < R := by
    by_contra hcon
    push Not at hcon
    have h0 := hφ0 xs hcon
    have hle : u x₁ ≤ u xs := hxsmax (Metric.mem_closedBall_self hRpos.le)
    have := abs_le.mp (hFF xs hxsΩ)
    have : u xs ≤ 1 / 4 := by simp only [hu, hW, h0]; linarith
    linarith
  have hloc : IsLocalMax u xs := hxsmax.isLocalMax
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr hxsball))
      Metric.ball_subset_closedBall)
  have hmp := max_principle (b := b) hopen huC hxsΩ hloc (ha xs hxsΩ)
  have e1 : Lop a b u xs = 1 * Lop a b W xs + 1 * Lop a b (φ : EuclideanSpace ℝ (Fin d) → ℝ) xs :=
    Lop_lin hopen hWC hφC2.contDiffOn hxsΩ 1 1
  have e2 : Lop a b W xs = lam * Lop a b F₁ xs + (-lam) * Lop a b F₂ xs :=
    Lop_lin hopen hC1.1 hC2.1 hxsΩ lam (-lam)
  have e3 : Lop a b F₁ xs = p.2 ⟨xs, subset_closure hxsΩ⟩ := by
    rw [← restr_eq _ hxsΩ]; exact (hL1 xs hxsΩ).symm
  have e4 : Lop a b F₂ xs = p'.2 ⟨xs, subset_closure hxsΩ⟩ := by
    rw [← restr_eq _ hxsΩ]; exact (hL2 xs hxsΩ).symm
  have hgap := hDK xs hxsΩ (Metric.mem_closedBall.mp hxsK)
  have k1 := abs_lt.mp (hpt _ _ ⟨xs, subset_closure hxsΩ⟩ hg1)
  have k2 := abs_lt.mp (hpt _ _ ⟨xs, subset_closure hxsΩ⟩ hg2)
  have hMx := abs_le.mp ((Real.norm_eq_abs _).symm ▸ hM xs hxsK)
  have hgap2 : δ / 4 ≤ p.2 ⟨xs, subset_closure hxsΩ⟩ - p'.2 ⟨xs, subset_closure hxsΩ⟩ := by
    linarith
  have hfin : lam * (δ / 4) ≤ lam * (p.2 ⟨xs, subset_closure hxsΩ⟩
      - p'.2 ⟨xs, subset_closure hxsΩ⟩) := mul_le_mul_of_nonneg_left hgap2 hlampos.le
  rw [e1, e2, e3, e4] at hmp
  have hMabs : M ≤ |M| := le_abs_self M
  nlinarith

end P74866daf

-- Single-valuedness of the closed obliquely reflected diffusion graph.
open EthierKurtz in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂ := by
  intro A f g₁ g₂ h₁ h₂
  have haC : ∀ i j, ContinuousOn (fun x => a x i j) Ω := fun i j => (haHolder i j).1
  have hbC : ContinuousOn b Ω :=
    P74866daf.continuousOn_of_components (fun i => (hbHolder i).1)
  ext z
  exact le_antisymm (P74866daf.closure_le hopen ha haC hbC h₁ h₂ z)
    (P74866daf.closure_le hopen ha haC hbC h₂ h₁ z)
