-- Prove2me | solution 1 for DCPenalty.Penalty.eq_3_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:40:08.314013+00:00
-- url     : https://prove2.me/submissions/939712ff-c42b-4fe6-a497-808cfcc1b962

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

end DCPAux

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

namespace DCPAux

/-- The `φ̂`-model constraint along the segment from `x̄` to `w`, eventually negative. -/
lemma model_seg_eventually_neg {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar)
    {w : EuclideanSpace ℝ (Fin n)} (hwY : w ∈ P.Y jj xbar)
    (hw : ∀ i ∈ P.Ieq xbar,
      P.φ i.succ w + P.ζ i.succ w - lin (P.ψ i.succ (jj i)) xbar w < 0) (i : Fin m) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      P.phiHat i.succ xbar (xbar + t • (w - xbar)) + P.ζ i.succ (xbar + t • (w - xbar)) -
        lin (P.ψ i.succ (jj i)) xbar (xbar + t • (w - xbar)) < 0 := by
  have hxS : xbar ∈ P.S := hP.X_subset_S hfeas.1
  have hwS : w ∈ P.S := hP.X_subset_S hwY.1
  set q : ℝ → ℝ := fun t =>
    P.phiHat i.succ xbar (xbar + t • (w - xbar)) + P.ζ i.succ (xbar + t • (w - xbar)) -
        lin (P.ψ i.succ (jj i)) xbar (xbar + t • (w - xbar)) with hq
  show ∀ᶠ t in 𝓝[>] (0:ℝ), q t < 0
  by_cases hi : i ∈ P.Ieq xbar
  · -- active: q t ≤ t * (h(w) + L t ‖w - x̄‖² / 2)
    set hw' := P.φ i.succ w + P.ζ i.succ w - lin (P.ψ i.succ (jj i)) xbar w
    have hneg : hw' < 0 := hw i hi
    have hlim : Tendsto (fun t : ℝ => hw' + P.L i.succ * t * ‖w - xbar‖ ^ 2 / 2) (𝓝[>] 0)
        (𝓝 (hw' + P.L i.succ * 0 * ‖w - xbar‖ ^ 2 / 2)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((continuous_const.add (((continuous_const.mul continuous_id).mul
        continuous_const).div_const 2))).tendsto 0
    simp only [mul_zero, zero_mul, zero_div, add_zero] at hlim
    have hev1 := hlim.eventually (gt_mem_nhds hneg)
    have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      (gt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev1, hev2, self_mem_nhdsWithin] with t ht1 ht2 ht0
    have ht0' : (0:ℝ) < t := ht0
    set z := xbar + t • (w - xbar) with hz
    have hzc : z = (1 - t) • xbar + t • w := by
      rw [hz, smul_sub, sub_smul, one_smul]; abel
    -- convexity of φ_i and ζ_i along the segment
    have hc1 := (hP.φ_convex i.succ).2 hxS hwS (by linarith : (0:ℝ) ≤ 1 - t) ht0'.le
      (by ring)
    have hc2 := (hP.ζ_convex i.succ).2 hxS hwS (by linarith : (0:ℝ) ≤ 1 - t) ht0'.le
      (by ring)
    rw [← hzc] at hc1 hc2
    simp only [smul_eq_mul] at hc1 hc2
    have hzS : z ∈ P.S := by
      rw [hzc]; exact hP.convex_S hxS hwS (by linarith) ht0'.le (by ring)
    -- gradient inequality
    have hg := grad_ineq (hP.φ_convex i.succ) hxS hzS (diffAt_of_C1 hP.isOpen_S (hP.φ_C1 i.succ) hxS)
    have h0 : P.φ i.succ xbar + P.ζ i.succ xbar - P.ψ i.succ (jj i) xbar = 0 := by
      have := model_at_xbar P hjj i
      simp only [lin, sub_self, map_zero, add_zero] at this
      rw [this]; exact hi
    have hlinz : lin (P.ψ i.succ (jj i)) xbar z = (1 - t) * P.ψ i.succ (jj i) xbar +
        t * lin (P.ψ i.succ (jj i)) xbar w := by
      simp only [lin, hz, add_sub_cancel_left, map_smul, smul_eq_mul]; ring
    have hnorm : ‖z - xbar‖ ^ 2 = t ^ 2 * ‖w - xbar‖ ^ 2 := by
      rw [hz, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0'.le]; ring
    simp only [hq, DCProblem.phiHat]
    rw [hlinz, hnorm]
    have hL := hP.L_nonneg i.succ
    have key : P.φ i.succ xbar + (fderiv ℝ (P.φ i.succ) xbar) (z - xbar) +
        P.L i.succ * (t ^ 2 * ‖w - xbar‖ ^ 2) / 2 + P.ζ i.succ z -
        ((1 - t) * P.ψ i.succ (jj i) xbar + t * lin (P.ψ i.succ (jj i)) xbar w) ≤
        t * (hw' + P.L i.succ * t * ‖w - xbar‖ ^ 2 / 2) := by
      simp only [hw']
      nlinarith
    have : t * (hw' + P.L i.succ * t * ‖w - xbar‖ ^ 2 / 2) < 0 := mul_neg_of_pos_of_neg ht0' ht1
    linarith
  · -- inactive: continuity at `t = 0`
    have hq0 : q 0 < 0 := by
      have := model_at_xbar P hjj i
      simp only [hq, zero_smul, add_zero, DCProblem.phiHat, sub_self, map_zero, norm_zero]
      simp only [lin, sub_self, map_zero, add_zero] at this ⊢
      norm_num
      have h2 := lt_of_le_of_ne (hfeas.2 i) hi
      linarith
    have hcont : ContinuousAt q 0 := by
      have hpath : Continuous (fun t : ℝ => xbar + t • (w - xbar)) := by fun_prop
      have hpath0 : (fun t : ℝ => xbar + t • (w - xbar)) 0 = xbar := by simp
      have c2 : ContinuousAt (fun t : ℝ => P.ζ i.succ (xbar + t • (w - xbar))) 0 := by
        apply ContinuousAt.comp (g := P.ζ i.succ)
        · simp only [zero_smul, add_zero]
          exact (hP.ζ_cont i.succ).continuousAt (hP.isOpen_S.mem_nhds hxS)
        · exact hpath.continuousAt
      have c1 : Continuous (fun t : ℝ => P.phiHat i.succ xbar (xbar + t • (w - xbar))) := by
        unfold DCProblem.phiHat; fun_prop
      have c3 : Continuous (fun t : ℝ => lin (P.ψ i.succ (jj i)) xbar (xbar + t • (w - xbar))) := by
        unfold lin; fun_prop
      exact (c1.continuousAt.add c2).sub c3.continuousAt
    exact (hcont.tendsto.eventually (gt_mem_nhds hq0)).filter_mono nhdsWithin_le_nhds

end DCPAux

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar)
    {xhat : EuclideanSpace ℝ (Fin n)} (hxhat : xhat ∈ P.Y jj xbar)
    (h318 : ∀ i ∈ P.Ieq xbar,
      P.φ i.succ xhat + P.ζ i.succ xhat - lin (P.ψ i.succ (jj i)) xbar xhat < 0) :
    ∀ τ ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ P.Y jj xbar, ∃ that ∈ Set.Ioo (0 : ℝ) 1,
      xbar + that • (((1 - τ) • x + τ • xhat) - xbar) ∈ P.Y jj xbar ∧
      ∀ i : Fin m,
        P.phiHat i.succ xbar (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) +
          P.ζ i.succ (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) -
          lin (P.ψ i.succ (jj i)) xbar (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) < 0 := by
  intro τ hτ x hx
  have hYc := DCPAux.convex_Y P hP xbar jj
  have hxbarY := DCPAux.xbar_mem_Y P hfeas hjj
  set w := (1 - τ) • x + τ • xhat with hwdef
  have hwY : w ∈ P.Y jj xbar := hYc hx hxhat (by linarith [hτ.2]) hτ.1.le (by ring)
  have hw : ∀ i ∈ P.Ieq xbar,
      P.φ i.succ w + P.ζ i.succ w - lin (P.ψ i.succ (jj i)) xbar w < 0 := by
    intro i hi
    have hxS := hP.X_subset_S hx.1
    have hxhS := hP.X_subset_S hxhat.1
    have h1 := (hP.φ_convex i.succ).2 hxS hxhS (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ) hτ.1.le
      (by ring)
    have h2 := (hP.ζ_convex i.succ).2 hxS hxhS (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ) hτ.1.le
      (by ring)
    simp only [smul_eq_mul] at h1 h2
    have h3 : lin (P.ψ i.succ (jj i)) xbar w = (1 - τ) * lin (P.ψ i.succ (jj i)) xbar x +
        τ * lin (P.ψ i.succ (jj i)) xbar xhat := by
      simp only [lin, hwdef]
      have : (1 - τ) • x + τ • xhat - xbar = (1 - τ) • (x - xbar) + τ • (xhat - xbar) := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have hx' := hx.2 i
    have hxh' := h318 i hi
    rw [h3]
    rw [← hwdef] at h1 h2
    have hτ1 := hτ.1
    have k1 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ) hx'
    have k2 := mul_neg_of_pos_of_neg hτ1 hxh'
    nlinarith
  have hall : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i : Fin m,
      P.phiHat i.succ xbar (xbar + t • (w - xbar)) + P.ζ i.succ (xbar + t • (w - xbar)) -
        lin (P.ψ i.succ (jj i)) xbar (xbar + t • (w - xbar)) < 0 := by
    rw [Filter.eventually_all]
    exact DCPAux.model_seg_eventually_neg P hP hfeas hjj hwY hw
  have hlt1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht1, ht0⟩ := (hall.and (hlt1.and self_mem_nhdsWithin)).exists
  refine ⟨t, ⟨ht0, ht1⟩, ?_, ht⟩
  have : xbar + t • (w - xbar) = (1 - t) • xbar + t • w := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  exact hYc hxbarY hwY (by linarith) (le_of_lt ht0) (by ring)
