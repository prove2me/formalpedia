-- Prove2me | solution 1 for DCPenalty.Penalty.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:45:06.120705+00:00
-- url     : https://prove2.me/submissions/2d6959dd-3a32-41fc-9769-fceade86b17a

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

namespace DCPAux

variable {n : ℕ}

/-- slope form of the directional derivative from a one-dimensional derivative. -/
lemma dirDeriv_of_hasDerivWithinAt (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (h : HasDerivWithinAt (fun t : ℝ => f (x + t • d)) c (Set.Ioi 0) 0) :
    HasOneSidedDirDeriv f x d c := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  unfold HasOneSidedDirDeriv
  have hs : Set.Ioi (0:ℝ) \ {0} = Set.Ioi 0 := by
    ext t; simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro ht; exact ⟨ht, ht.ne'⟩
  rw [hs] at h
  refine h.congr ?_
  intro t
  simp [slope, div_eq_inv_mul]

/-- A convex function on an open set has one-sided directional derivatives in every direction. -/
lemma dirDeriv_exists_of_convex {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hS : IsOpen S) (hf : ConvexOn ℝ S f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (d : EuclideanSpace ℝ (Fin n)) :
    ∃ c, HasOneSidedDirDeriv f x d c := by
  set S' : Set ℝ := (fun t : ℝ => x + t • d) ⁻¹' S with hS'
  have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
  have hopen : IsOpen S' := hS.preimage hcont
  have h0 : (0:ℝ) ∈ S' := by simp [hS', hx]
  have hconv : ConvexOn ℝ S' (fun t : ℝ => f (x + t • d)) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb μ ν hμ hν hμν
      have := hf.1 ha hb hμ hν hμν
      simp only [hS', Set.mem_preimage, smul_eq_mul] at this ⊢
      convert this using 1
      have hμ' : μ = 1 - ν := by linarith
      subst hμ'
      simp only [add_smul, smul_add, mul_smul, sub_smul, one_smul]
      abel
    · intro a ha b hb μ ν hμ hν hμν
      have := hf.2 ha hb hμ hν hμν
      simp only [smul_eq_mul] at this ⊢
      convert this using 2
      have hμ' : μ = 1 - ν := by linarith
      subst hμ'
      simp only [add_smul, smul_add, mul_smul, sub_smul, one_smul]
      abel
  have hint : (0:ℝ) ∈ interior S' := by rw [hopen.interior_eq]; exact h0
  exact ⟨_, dirDeriv_of_hasDerivWithinAt f x d _
    (ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior hconv hint)⟩

/-- A function differentiable at `x` has directional derivative `fderiv f x d`. -/
lemma dirDeriv_of_differentiableAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x) (d : EuclideanSpace ℝ (Fin n)) :
    HasOneSidedDirDeriv f x d (fderiv ℝ f x d) := by
  apply dirDeriv_of_hasDerivWithinAt
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • d) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0:ℝ) h1).hasDerivWithinAt

/-- Uniqueness of the directional derivative. -/
lemma dirDeriv_unique {f : EuclideanSpace ℝ (Fin n) → ℝ} {x d : EuclideanSpace ℝ (Fin n)}
    {c c' : ℝ} (h : HasOneSidedDirDeriv f x d c) (h' : HasOneSidedDirDeriv f x d c') : c = c' :=
  tendsto_nhds_unique h h'

/-- Convex continuous functions on an open set are Lipschitz on a ball around each point. -/
lemma lip_ball_of_convex {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hS : IsOpen S) (hf : ConvexOn ℝ S f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    ∃ K r, 0 < r ∧ LipschitzOnWith K f (Metric.ball x r) := by
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitzOn hS hx
  rw [hS.nhdsWithin_eq hx, Metric.mem_nhds_iff] at ht
  obtain ⟨r, hr, hrt⟩ := ht
  exact ⟨K, r, hr, hK.mono hrt⟩

/-- `C¹` functions are Lipschitz on a ball around each point of an open set. -/
lemma lip_ball_of_C1 {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    ∃ K r, 0 < r ∧ LipschitzOnWith K f (Metric.ball x r) := by
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hS.mem_nhds hx)).exists_lipschitzOnWith
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨r, hr, hrt⟩ := ht
  exact ⟨K, r, hr, hK.mono hrt⟩

/-- Hadamard-type directional derivative along sequences for locally Lipschitz functions. -/
lemma hadamard {f : EuclideanSpace ℝ (Fin n) → ℝ} {x d : EuclideanSpace ℝ (Fin n)} {c : ℝ}
    {K : NNReal} {r : ℝ} (hr : 0 < r) (hK : LipschitzOnWith K f (Metric.ball x r))
    (hdir : HasOneSidedDirDeriv f x d c) {τ : ℕ → ℝ} {v : ℕ → EuclideanSpace ℝ (Fin n)}
    (hτpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 d)) :
    Tendsto (fun k => (f (x + τ k • v k) - f x) / τ k) atTop (𝓝 c) := by
  have hτ' : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hτ, Eventually.of_forall hτpos⟩
  have h1 : Tendsto (fun k => (f (x + τ k • d) - f x) / τ k) atTop (𝓝 c) := hdir.comp hτ'
  have h2 : Tendsto (fun k => (f (x + τ k • v k) - f (x + τ k • d)) / τ k) atTop (𝓝 0) := by
    have hvd : Tendsto (fun k => ‖v k - d‖) atTop (𝓝 0) := by
      have := (hv.sub_const d)
      simpa using this.norm
    have hbound : Tendsto (fun k => (K:ℝ) * ‖v k - d‖) atTop (𝓝 0) := by
      simpa using hvd.const_mul (K:ℝ)
    -- eventually both points are in the ball
    have hτv : Tendsto (fun k => τ k • v k) atTop (𝓝 0) := by
      simpa using hτ.smul hv
    have hτd : Tendsto (fun k => τ k • d) atTop (𝓝 0) := by
      simpa using hτ.smul_const d
    have e1 : ∀ᶠ k in atTop, x + τ k • v k ∈ Metric.ball x r := by
      have := (Metric.tendsto_nhds.1 hτv) r hr
      filter_upwards [this] with k hk
      simpa [Metric.mem_ball, dist_eq_norm] using hk
    have e2 : ∀ᶠ k in atTop, x + τ k • d ∈ Metric.ball x r := by
      have := (Metric.tendsto_nhds.1 hτd) r hr
      filter_upwards [this] with k hk
      simpa [Metric.mem_ball, dist_eq_norm] using hk
    apply squeeze_zero_norm' _ hbound
    filter_upwards [e1, e2] with k hk1 hk2
    have hl := hK.dist_le_mul _ hk1 _ hk2
    rw [Real.dist_eq, dist_eq_norm] at hl
    have hx' : x + τ k • v k - (x + τ k • d) = τ k • (v k - d) := by
      rw [smul_sub]; abel
    rw [hx', norm_smul, Real.norm_of_nonneg (hτpos k).le] at hl
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hτpos k), div_le_iff₀ (hτpos k)]
    nlinarith [hτpos k]
  have := h1.add h2
  simp only [add_zero] at this
  refine this.congr ?_
  intro k
  field_simp
  ring

/-- Monotonicity of the Bouligand tangent cone. -/
lemma tangentConeB_mono {A B : Set (EuclideanSpace ℝ (Fin n))} (h : A ⊆ B)
    (x : EuclideanSpace ℝ (Fin n)) : tangentConeB A x ⊆ tangentConeB B x := by
  rintro d ⟨xs, τ, hxs, h1, h2, h3, h4⟩
  exact ⟨xs, τ, fun k => h (hxs k), h1, h2, h3, h4⟩

/-- Unpack a tangent direction as `xs k = x + τ k • v k`. -/
lemma tc_seq {A : Set (EuclideanSpace ℝ (Fin n))} {x d : EuclideanSpace ℝ (Fin n)}
    (hd : d ∈ tangentConeB A x) :
    ∃ xs : ℕ → EuclideanSpace ℝ (Fin n), ∃ τ : ℕ → ℝ, ∃ v : ℕ → EuclideanSpace ℝ (Fin n),
      (∀ k, xs k ∈ A) ∧ (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 d) ∧
      (∀ k, xs k = x + τ k • v k) ∧ Tendsto xs atTop (𝓝 x) := by
  obtain ⟨xs, τ, hxs, hlim, hτpos, hτ, hv⟩ := hd
  refine ⟨xs, τ, fun k => (τ k)⁻¹ • (xs k - x), hxs, hτpos, hτ, hv, fun k => ?_, hlim⟩
  simp only [smul_smul, mul_inv_cancel₀ (hτpos k).ne', one_smul]
  abel

/-- Hadamard limit for a `C¹` function. -/
lemma hadamard_C1 {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S) {x d : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    {τ : ℕ → ℝ} {v : ℕ → EuclideanSpace ℝ (Fin n)}
    (hτpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 d)) :
    Tendsto (fun k => (f (x + τ k • v k) - f x) / τ k) atTop (𝓝 (fderiv ℝ f x d)) := by
  obtain ⟨K, r, hr, hK⟩ := lip_ball_of_C1 hS hf hx
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hS.mem_nhds hx)
  exact hadamard hr hK (dirDeriv_of_differentiableAt hdiff d) hτpos hτ hv

/-- Hadamard limit for a convex function on an open set. -/
lemma hadamard_convex {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hS : IsOpen S) (hf : ConvexOn ℝ S f) {x d : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) {c : ℝ}
    (hc : HasOneSidedDirDeriv f x d c)
    {τ : ℕ → ℝ} {v : ℕ → EuclideanSpace ℝ (Fin n)}
    (hτpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 d)) :
    Tendsto (fun k => (f (x + τ k • v k) - f x) / τ k) atTop (𝓝 c) := by
  obtain ⟨K, r, hr, hK⟩ := lip_ball_of_convex hS hf hx
  exact hadamard hr hK hc hτpos hτ hv

/-- Linear part. -/
lemma lin_quot (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) {d : EuclideanSpace ℝ (Fin n)}
    {τ : ℕ → ℝ} {v : ℕ → EuclideanSpace ℝ (Fin n)} (hτpos : ∀ k, 0 < τ k)
    (hv : Tendsto v atTop (𝓝 d)) :
    Tendsto (fun k => L (τ k • v k) / τ k) atTop (𝓝 (L d)) := by
  have h := (L.continuous.tendsto d).comp hv
  refine h.congr (fun k => ?_)
  simp only [Function.comp_apply, map_smul, smul_eq_mul]
  field_simp [(hτpos k).ne']

/-- For a convex function, the directional derivative towards `y` is at most `f y − f x`. -/
lemma dirDeriv_le_of_convex {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ S f)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) {c : ℝ}
    (hc : HasOneSidedDirDeriv f x (y - x) c) : c ≤ f y - f x := by
  apply le_of_tendsto hc
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 := by
    have : ∀ᶠ δ in 𝓝 (0:ℝ), δ < 1 := gt_mem_nhds one_pos
    exact this.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with δ h1 h0
  have h0' : (0:ℝ) < δ := h0
  have hconv := hf.2 hx hy (by linarith : (0:ℝ) ≤ 1 - δ) h0'.le (by ring)
  have heq : (1 - δ) • x + δ • y = x + δ • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq] at hconv
  simp only [smul_eq_mul] at hconv
  rw [div_le_iff₀ h0']
  nlinarith

/-- Gradient inequality for a convex function differentiable at `x`. -/
lemma grad_ineq {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ S f)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) (hd : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have := dirDeriv_le_of_convex hf hx hy (dirDeriv_of_differentiableAt hd (y - x))
  linarith

lemma diffAt_of_C1 {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    DifferentiableAt ℝ f x :=
  (hf.differentiableOn one_ne_zero).differentiableAt (hS.mem_nhds hx)

variable {m : ℕ}

/-- The constraint model `φ_i + ζ_i − ℓ_{ψ_{i,j}}(·; x̄)` agrees with `g_i` at `x̄` when `j` is
active. -/
lemma model_at_xbar (P : DCProblem n m) {xbar : EuclideanSpace ℝ (Fin n)}
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar) (i : Fin m) :
    P.φ i.succ xbar + P.ζ i.succ xbar - lin (P.ψ i.succ (jj i)) xbar xbar = P.g i xbar := by
  have h := hjj i
  simp only [DCProblem.Jact, Set.mem_setOf_eq] at h
  simp only [lin, sub_self, map_zero, add_zero, DCProblem.g, h]

/-- `x̄ ∈ Y_jj(x̄)` for `x̄ ∈ Ω`, `jj ∈ 𝓙(x̄)`. -/
lemma xbar_mem_Y (P : DCProblem n m) {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar) : xbar ∈ P.Y jj xbar :=
  ⟨hfeas.1, fun i => by rw [model_at_xbar P hjj i]; exact hfeas.2 i⟩

/-- Convexity of `Y_jj(x̄)`. -/
lemma convex_Y (P : DCProblem n m) (hP : P.Standing) (xbar : EuclideanSpace ℝ (Fin n))
    (jj : (i : Fin m) → Fin (P.J i.succ)) : Convex ℝ (P.Y jj xbar) := by
  intro a ha b hb μ ν hμ hν hμν
  refine ⟨hP.convex_X ha.1 hb.1 hμ hν hμν, fun i => ?_⟩
  have haS := hP.X_subset_S ha.1
  have hbS := hP.X_subset_S hb.1
  have h1 := (hP.φ_convex i.succ).2 haS hbS hμ hν hμν
  have h2 := (hP.ζ_convex i.succ).2 haS hbS hμ hν hμν
  have h3 : lin (P.ψ i.succ (jj i)) xbar (μ • a + ν • b) =
      μ * lin (P.ψ i.succ (jj i)) xbar a + ν * lin (P.ψ i.succ (jj i)) xbar b := by
    have hμ' : μ = 1 - ν := by linarith
    subst hμ'
    simp only [lin]
    have : (1 - ν) • a + ν • b - xbar = (1 - ν) • (a - xbar) + ν • (b - xbar) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_sub, map_sub]
    ring
  have ha' := ha.2 i
  have hb' := hb.2 i
  simp only [smul_eq_mul] at h1 h2
  rw [h3]
  nlinarith

/-- Under a Slater-type direction for `jj`, some point of `Y_jj(x̄)` strictly satisfies the
active linearised constraints (proof of (3.18)). -/
lemma exists_slater_point {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar)
    (h24 : ∃ d ∈ tangentConeB P.X xbar, ∀ i ∈ P.Ieq xbar,
      ∃ c, HasOneSidedDirDeriv (P.ζ i.succ) xbar d c ∧
        fderiv ℝ (P.φ i.succ) xbar d + c - fderiv ℝ (P.ψ i.succ (jj i)) xbar d < 0) :
    ∃ xhat ∈ P.Y jj xbar, ∀ i ∈ P.Ieq xbar,
      P.φ i.succ xhat + P.ζ i.succ xhat - lin (P.ψ i.succ (jj i)) xbar xhat < 0 := by
  obtain ⟨d, hdX, hdi⟩ := h24
  have hxS : xbar ∈ P.S := hP.X_subset_S hfeas.1
  obtain ⟨xs, τ, v, hxsX, hτpos, hτ, hv, hxs_eq, hxs_lim⟩ := tc_seq hdX
  set h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun i y =>
    P.φ i.succ y + P.ζ i.succ y - lin (P.ψ i.succ (jj i)) xbar y with hh
  have hev : ∀ᶠ k in atTop, ∀ i, h i (xs k) < 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ P.Ieq xbar
    · obtain ⟨c, hc, hlt⟩ := hdi i hi
      have h1 := hadamard_C1 hP.isOpen_S (hP.φ_C1 i.succ) hxS hτpos hτ hv (d := d)
      have h2 := hadamard_convex hP.isOpen_S (hP.ζ_convex i.succ) hxS hc hτpos hτ hv
      have h3 := lin_quot (fderiv ℝ (P.ψ i.succ (jj i)) xbar) hτpos hv
      have h4 := (h1.add h2).sub h3
      have hlim : Tendsto (fun k => h i (xs k) / τ k) atTop
          (𝓝 (fderiv ℝ (P.φ i.succ) xbar d + c - fderiv ℝ (P.ψ i.succ (jj i)) xbar d)) := by
        refine h4.congr (fun k => ?_)
        have h0 : h i xbar = 0 := by
          have := model_at_xbar P hjj i
          simp only [hh]; rw [this]; exact hi
        have h0' : P.φ i.succ xbar + P.ζ i.succ xbar - P.ψ i.succ (jj i) xbar = 0 := by
          have := h0; simp only [hh, lin, sub_self, map_zero, add_zero] at this; exact this
        rw [hxs_eq k]
        simp only [hh, lin, add_sub_cancel_left]
        field_simp [(hτpos k).ne']
        linarith [h0']
      filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with k hk
      have := hτpos k
      by_contra hcon
      push_neg at hcon
      have : 0 ≤ h i (xs k) / τ k := div_nonneg hcon this.le
      linarith
    · have hneg : h i xbar < 0 := by
        have := model_at_xbar P hjj i
        simp only [hh]; rw [this]
        exact lt_of_le_of_ne (hfeas.2 i) hi
      have hcont : ContinuousAt (h i) xbar := by
        have c1 : ContinuousAt (P.φ i.succ) xbar :=
          ((hP.φ_C1 i.succ).continuousOn.continuousAt (hP.isOpen_S.mem_nhds hxS))
        have c2 : ContinuousAt (P.ζ i.succ) xbar :=
          ((hP.ζ_cont i.succ).continuousAt (hP.isOpen_S.mem_nhds hxS))
        have c3 : Continuous (lin (P.ψ i.succ (jj i)) xbar) := by
          unfold lin; fun_prop
        exact (c1.add c2).sub c3.continuousAt
      exact (hcont.tendsto.comp hxs_lim).eventually (gt_mem_nhds hneg)
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨xs k, ⟨hxsX k, fun i => (hk i).le⟩, fun i _ => hk i⟩


/-- The Bouligand tangent cone is closed. -/
lemma tangentConeB_closed {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : IsClosed (tangentConeB A x) := by
  apply IsSeqClosed.isClosed
  intro D d hD hlim
  have hex : ∀ j : ℕ, ∃ y ∈ A, ∃ t : ℝ, 0 < t ∧ dist y x < 1 / ((j:ℝ) + 1) ∧
      t < 1 / ((j:ℝ) + 1) ∧ dist (t⁻¹ • (y - x)) (D j) < 1 / ((j:ℝ) + 1) := by
    intro j
    obtain ⟨xs, τ, hxs, h1, h2, h3, h4⟩ := hD j
    have hε : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
    have e1 := (Metric.tendsto_nhds.1 h1) _ hε
    have e2 := (Metric.tendsto_nhds.1 h3) _ hε
    have e3 := (Metric.tendsto_nhds.1 h4) _ hε
    obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
    refine ⟨xs k, hxs k, τ k, h2 k, hk1, ?_, hk3⟩
    have := hk2
    rw [Real.dist_eq, sub_zero, abs_of_pos (h2 k)] at this
    exact this
  choose y hyA t ht0 hy ht hv using hex
  have hj : Tendsto (fun j : ℕ => 1 / ((j:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨y, t, hyA, ?_, ht0, ?_, ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (hy j).le) hj
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hj
    rw [Real.dist_eq, sub_zero, abs_of_pos (ht0 j)]
    exact (ht j).le
  · rw [tendsto_iff_dist_tendsto_zero]
    have hD' : Tendsto (fun j => dist (D j) d) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero.1 hlim)
    have hsum := hj.add hD'
    rw [add_zero] at hsum
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hsum
    exact (dist_triangle _ (D j) d).trans (by linarith [hv j])

/-- `Ω_𝕁 ⊆ Ω`. -/
lemma Ωj_subset_Ω {n m : ℕ} (P : DCProblem n m) (jj : (i : Fin m) → Fin (P.J i.succ)) :
    P.Ωj jj ⊆ P.Ω := by
  intro y hy
  refine ⟨hy.1, fun i => ?_⟩
  have h1 := hy.2 i
  have h2 : P.ψ i.succ (jj i) y ≤ P.psi i.succ y :=
    Finset.le_sup' (fun j => P.ψ i.succ j y) (Finset.mem_univ (jj i))
  simp only [DCProblem.g]
  linarith

/-- `Y_𝕁(x̄) ⊆ Ω_𝕁` (convexity of the pieces `ψ_{i,j}`). -/
lemma Y_subset_Ωj {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ P.X)
    (jj : (i : Fin m) → Fin (P.J i.succ)) : P.Y jj xbar ⊆ P.Ωj jj := by
  intro y hy
  refine ⟨hy.1, fun i => ?_⟩
  have hxS := hP.X_subset_S hxbar
  have hyS := hP.X_subset_S hy.1
  have hg := grad_ineq (hP.ψ_convex i.succ (jj i)) hxS hyS
    (diffAt_of_C1 hP.isOpen_S (hP.ψ_C1 i.succ (jj i)) hxS)
  have := hy.2 i
  simp only [lin] at this
  linarith

end DCPAux

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) :
    ∀ xbar ∈ P.Ω, tangentConeB P.Ω xbar = ⋃ jj ∈ P.Jtup xbar, tangentConeB (P.Ωj jj) xbar := by
  intro xbar hxbar
  have hxS : xbar ∈ P.S := hP.X_subset_S hxbar.1
  apply Set.Subset.antisymm
  · rintro d ⟨xs, τ, hxs, hlim, hτpos, hτ, hv⟩
    -- a maximizing tuple at each `xs k`
    have hmax : ∀ k, ∀ i : Fin m, ∃ j : Fin (P.J i.succ), P.psi i.succ (xs k) = P.ψ i.succ j (xs k) := by
      intro k i
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (⟨⟨0, P.J_pos i.succ⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin (P.J i.succ))).Nonempty) (fun j => P.ψ i.succ j (xs k))
      exact ⟨j, hj⟩
    choose jk hjk using hmax
    -- `xs k ∈ Ω_{jk k}`
    have hmem : ∀ k, xs k ∈ P.Ωj (jk k) := by
      intro k
      refine ⟨(hxs k).1, fun i => ?_⟩
      have := (hxs k).2 i
      simp only [DCProblem.g] at this
      rw [hjk k i] at this
      exact this
    -- eventually the maximizing tuple is active at `xbar`
    have hnb := hP.isOpen_S.mem_nhds hxS
    have hgood : ∀ᶠ k in atTop, ∀ i : Fin m, jk k i ∈ P.Jact i.succ xbar := by
      have hev : ∀ᶠ k in atTop, ∀ i : Fin m, ∀ j : Fin (P.J i.succ), j ∉ P.Jact i.succ xbar →
          P.ψ i.succ j (xs k) < P.psi i.succ (xs k) := by
        rw [Filter.eventually_all]; intro i
        rw [Filter.eventually_all]; intro j
        by_cases hj : j ∈ P.Jact i.succ xbar
        · exact Eventually.of_forall (fun _ h => absurd hj h)
        · have hlt : P.ψ i.succ j xbar < P.psi i.succ xbar := by
            have h1 : P.ψ i.succ j xbar ≤ P.psi i.succ xbar :=
              Finset.le_sup' (fun j => P.ψ i.succ j xbar) (Finset.mem_univ j)
            exact lt_of_le_of_ne h1 (fun h => hj h.symm)
          have c1 : ContinuousAt (P.ψ i.succ j) xbar :=
            (hP.ψ_C1 i.succ j).continuousOn.continuousAt hnb
          have c2 : ContinuousAt (P.psi i.succ) xbar := by
            unfold DCProblem.psi
            exact ContinuousAt.finset_sup'_apply _
              (fun j _ => (hP.ψ_C1 i.succ j).continuousOn.continuousAt hnb)
          have := ((c2.sub c1).tendsto.comp hlim).eventually (lt_mem_nhds (sub_pos.2 hlt))
          filter_upwards [this] with k hk _
          simp only [Function.comp_apply, Pi.sub_apply] at hk
          linarith
      filter_upwards [hev] with k hk i
      by_contra hcon
      have := hk i (jk k i) hcon
      rw [hjk k i] at this
      exact lt_irrefl _ this
    -- pigeonhole: some tuple occurs infinitely often
    obtain ⟨jj, hjj⟩ := Finite.exists_infinite_fiber jk
    have hfreq : ∃ᶠ k in atTop, jk k = jj := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact Set.infinite_coe_iff.1 hjj
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hgood)
    have hjjA : jj ∈ P.Jtup xbar := by
      intro i
      have := (hφP 0).2 i
      rw [(hφP 0).1] at this
      exact this
    refine Set.mem_biUnion hjjA ⟨xs ∘ φ, τ ∘ φ, fun k => ?_, hlim.comp hφ.tendsto_atTop,
      fun k => hτpos _, hτ.comp hφ.tendsto_atTop, hv.comp hφ.tendsto_atTop⟩
    have := hmem (φ k)
    rw [(hφP k).1] at this
    exact this
  · intro d hd
    simp only [Set.mem_iUnion] at hd
    obtain ⟨jj, -, hd⟩ := hd
    exact DCPAux.tangentConeB_mono (DCPAux.Ωj_subset_Ω P jj) xbar hd
