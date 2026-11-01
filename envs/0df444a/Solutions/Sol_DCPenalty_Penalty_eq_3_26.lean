-- Prove2me | solution 1 for DCPenalty.Penalty.eq_3_26
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:42:32.698284+00:00
-- url     : https://prove2.me/submissions/16f749d5-b884-457f-9dca-0fca57fb3a72

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm
import Theorems.Thm_DCPenalty_Penalty_eq_3_10
import Theorems.Thm_DCPenalty_Penalty_eq_3_18
import Theorems.Thm_DCPenalty_Penalty_eq_3_20

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

/-- `ℓ_f(z; x̄)` is continuous in the base point `x̄` for `C¹` functions. -/
lemma lin_cont_base {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {xinf : EuclideanSpace ℝ (Fin n)} (hx : xinf ∈ S) (z : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun xb => lin f xb z) xinf := by
  unfold lin
  have h1 : ContinuousAt f xinf := hf.continuousOn.continuousAt (hS.mem_nhds hx)
  have h2 : ContinuousAt (fderiv ℝ f) xinf :=
    (hf.continuousOn_fderiv_of_isOpen hS le_rfl).continuousAt (hS.mem_nhds hx)
  have h3 : ContinuousAt (fun xb => z - xb) xinf := by fun_prop
  exact h1.add (h2.clm_apply h3)

lemma phiHat_cont_base {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) (i : Fin (m + 1))
    {xinf : EuclideanSpace ℝ (Fin n)} (hx : xinf ∈ P.S) (z : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun xb => P.phiHat i xb z) xinf := by
  have h := lin_cont_base hP.isOpen_S (hP.φ_C1 i) hx z
  have h4 : ContinuousAt (fun xb => P.L i * ‖z - xb‖ ^ 2 / 2) xinf := by fun_prop
  have := h.add h4
  refine this.congr (Eventually.of_forall fun xb => ?_)
  simp [DCProblem.phiHat, lin]

lemma F_cont {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xinf : EuclideanSpace ℝ (Fin n)} (hx : xinf ∈ P.S) : ContinuousAt P.F xinf := by
  have hnb := hP.isOpen_S.mem_nhds hx
  have h1 : ContinuousAt (P.φ 0) xinf := (hP.φ_C1 0).continuousOn.continuousAt hnb
  have h2 : ContinuousAt (P.ζ 0) xinf := (hP.ζ_cont 0).continuousAt hnb
  have h3 : ContinuousAt (P.psi 0) xinf := by
    unfold DCProblem.psi
    exact ContinuousAt.finset_sup'_apply _
      (fun j _ => (hP.ψ_C1 0 j).continuousOn.continuousAt hnb)
  exact (h1.add h2).sub h3

lemma Qrho_eq_of_neg {n m : ℕ} (P : DCProblem n m) {p ρ : ℝ} (hp : 1 ≤ p)
    (xb : EuclideanSpace ℝ (Fin n)) (j0 : Fin (P.J 0)) (jj : (i : Fin m) → Fin (P.J i.succ))
    (z : EuclideanSpace ℝ (Fin n))
    (hneg : ∀ i : Fin m, P.phiHat i.succ xb z + P.ζ i.succ z - lin (P.ψ i.succ (jj i)) xb z < 0) :
    P.Qrho p ρ xb j0 jj z = P.phiHat 0 xb z + P.ζ 0 z - lin (P.ψ 0 j0) xb z := by
  unfold DCProblem.Qrho
  have : ∀ i : Fin m,
      (max (P.phiHat i.succ xb z + P.ζ i.succ z - lin (P.ψ i.succ (jj i)) xb z) 0) ^ p = 0 := by
    intro i
    rw [max_eq_right (hneg i).le]
    exact Real.zero_rpow (by linarith)
  simp [this]

lemma Frho_ge {n m : ℕ} (P : DCProblem n m) {p ρ : ℝ} (hρ : 0 ≤ ρ)
    (x : EuclideanSpace ℝ (Fin n)) : P.F x ≤ P.Frho p ρ x := by
  unfold DCProblem.Frho
  have : 0 ≤ ∑ i : Fin m, (max (P.g i x) 0) ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (le_max_right _ _) _)
  nlinarith

lemma norm_sq_convex {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ‖(1 - t) • u + t • v‖ ^ 2 ≤ (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
  have h1 : ‖(1 - t) • u + t • v‖ ≤ (1 - t) * ‖u‖ + t * ‖v‖ := by
    calc ‖(1 - t) • u + t • v‖ ≤ ‖(1 - t) • u‖ + ‖t • v‖ := norm_add_le _ _
      _ = (1 - t) * ‖u‖ + t * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht0, Real.norm_of_nonneg (by linarith)]
  have h0 : 0 ≤ ‖(1 - t) • u + t • v‖ := norm_nonneg _
  have h2 : ‖(1 - t) • u + t • v‖ ^ 2 ≤ ((1 - t) * ‖u‖ + t * ‖v‖) ^ 2 := by
    exact pow_le_pow_left₀ h0 h1 2
  have h3 : ((1 - t) * ‖u‖ + t * ‖v‖) ^ 2 ≤ (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
    have : (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - ((1 - t) * ‖u‖ + t * ‖v‖) ^ 2 =
        t * (1 - t) * (‖u‖ - ‖v‖) ^ 2 := by ring
    have : 0 ≤ t * (1 - t) * (‖u‖ - ‖v‖) ^ 2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    linarith
  linarith

/-- Convexity of `ĥ_{0,j_0} = φ̂_0(·; x̄) + ζ_0 − ℓ_{ψ_{0,j_0}}(·; x̄)` along segments in `S`. -/
lemma hhat_convex {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    (xb : EuclideanSpace ℝ (Fin n)) (j0 : Fin (P.J 0)) {a b : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ P.S) (hb : b ∈ P.S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.phiHat 0 xb ((1 - t) • a + t • b) + P.ζ 0 ((1 - t) • a + t • b) -
        lin (P.ψ 0 j0) xb ((1 - t) • a + t • b) ≤
      (1 - t) * (P.phiHat 0 xb a + P.ζ 0 a - lin (P.ψ 0 j0) xb a) +
        t * (P.phiHat 0 xb b + P.ζ 0 b - lin (P.ψ 0 j0) xb b) := by
  have hz := (hP.ζ_convex 0).2 ha hb (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hz
  have hsplit : (1 - t) • a + t • b - xb = (1 - t) • (a - xb) + t • (b - xb) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  have hn := norm_sq_convex (a - xb) (b - xb) ht0 ht1
  rw [← hsplit] at hn
  have hL := hP.L_nonneg 0
  simp only [DCProblem.phiHat, lin, hsplit, map_add, map_smul, smul_eq_mul]
  rw [hsplit] at hn
  have hLn := mul_le_mul_of_nonneg_left hn hL
  nlinarith

end DCPAux

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {p ε ρ0 σ : ℝ} {η : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : P.IsPenaltyRun p ε ρ0 σ η x)
    {K : ℕ → ℕ} (hK : StrictMono K) {xinf : EuclideanSpace ℝ (Fin n)}
    (hlim : Tendsto (x ∘ K) atTop (𝓝 xinf))
    (hfeas : xinf ∈ P.Ω) (hact : (P.Ieq xinf).Nonempty) (hpscq : P.PSCQ xinf) :
    ∀ jj ∈ P.Jtup xinf, ∀ j0 ∈ P.Jact 0 xinf,
      xinf ∈ P.Y jj xinf ∧ ∀ y ∈ P.Y jj xinf,
        P.phiHat 0 xinf xinf + P.ζ 0 xinf - lin (P.ψ 0 j0) xinf xinf ≤
          P.phiHat 0 xinf y + P.ζ 0 y - lin (P.ψ 0 j0) xinf y := by
  intro jj hjj j0 hj0
  obtain ⟨_, hρ0, hσ, hp, _, hη, _, _⟩ := id hrun
  have hxS : xinf ∈ P.S := hP.X_subset_S hfeas.1
  have hxY := DCPAux.xbar_mem_Y P hfeas hjj
  refine ⟨hxY, fun y hy => ?_⟩
  set hh : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    P.phiHat 0 xinf z + P.ζ 0 z - lin (P.ψ 0 j0) xinf z with hhdef
  show hh xinf ≤ hh y
  -- value at `xinf` equals `F xinf`
  have hF : hh xinf = P.F xinf := by
    have h := hj0
    simp only [DCProblem.Jact, Set.mem_setOf_eq] at h
    simp only [hhdef, DCProblem.phiHat, lin, sub_self, map_zero, norm_zero, DCProblem.F, h]
    ring
  -- key step: `F xinf ≤ ĥ z` whenever all `φ̂`-model constraints are strict at `z ∈ X`
  have hkey : ∀ z ∈ P.X, (∀ i : Fin m, P.phiHat i.succ xinf z + P.ζ i.succ z -
      lin (P.ψ i.succ (jj i)) xinf z < 0) → P.F xinf ≤ hh z := by
    intro z hzX hneg
    have h310 := eq_3_10 P hP hrun hK hlim
    -- eventually the model constraints at base `x (K k)` are strict
    have hev : ∀ᶠ k in atTop, ∀ i : Fin m, P.phiHat i.succ (x (K k)) z + P.ζ i.succ z -
        lin (P.ψ i.succ (jj i)) (x (K k)) z < 0 := by
      rw [Filter.eventually_all]
      intro i
      have hc : ContinuousAt (fun xb => P.phiHat i.succ xb z + P.ζ i.succ z -
          lin (P.ψ i.succ (jj i)) xb z) xinf :=
        ((DCPAux.phiHat_cont_base P hP i.succ hxS z).add continuousAt_const).sub
          (DCPAux.lin_cont_base hP.isOpen_S (hP.ψ_C1 i.succ (jj i)) hxS z)
      exact (hc.tendsto.comp hlim).eventually (gt_mem_nhds (hneg i))
    have hineq : ∀ᶠ k in atTop, P.F (x (K k)) - η (K k) ≤
        P.phiHat 0 (x (K k)) z + P.ζ 0 z - lin (P.ψ 0 j0) (x (K k)) z := by
      filter_upwards [h310, hev] with k hk hk2
      have := hk j0 hj0 jj hjj z hzX
      rw [DCPAux.Qrho_eq_of_neg P hp _ j0 jj z hk2] at this
      have hρ : 0 ≤ ρ0 * σ ^ (K k) := by positivity
      have := DCPAux.Frho_ge P (p := p) hρ (x (K k))
      linarith
    have hl1 : Tendsto (fun k => P.F (x (K k)) - η (K k)) atTop (𝓝 (P.F xinf - 0)) :=
      ((DCPAux.F_cont P hP hxS).tendsto.comp hlim).sub (hη.comp hK.tendsto_atTop)
    have hc0 : ContinuousAt (fun xb => P.phiHat 0 xb z + P.ζ 0 z - lin (P.ψ 0 j0) xb z) xinf :=
      ((DCPAux.phiHat_cont_base P hP 0 hxS z).add continuousAt_const).sub
        (DCPAux.lin_cont_base hP.isOpen_S (hP.ψ_C1 0 j0) hxS z)
    have hl2 := hc0.tendsto.comp hlim
    rw [sub_zero] at hl1
    exact le_of_tendsto_of_tendsto hl1 hl2 hineq
  -- the Slater point and the curve `x(t, τ)`
  obtain ⟨xhat, hxhatY, h318⟩ := eq_3_18 P hP hfeas hact hpscq jj hjj
  have hyS := hP.X_subset_S hy.1
  have hxhS := hP.X_subset_S hxhatY.1
  have hτ : ∀ τ ∈ Set.Ioc (0:ℝ) 1, hh xinf ≤ (1 - τ) * hh y + τ * hh xhat := by
    intro τ hτ
    obtain ⟨t, ht, hzY, hzneg⟩ := eq_3_20 P hP hfeas hact hjj hxhatY h318 τ hτ y hy
    set w := (1 - τ) • y + τ • xhat with hw
    have hwS : w ∈ P.S := hP.convex_S hyS hxhS (by linarith [hτ.2]) hτ.1.le (by ring)
    have h1 := hkey _ hzY.1 hzneg
    rw [← hF] at h1
    have hzeq : xinf + t • (w - xinf) = (1 - t) • xinf + t • w := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hzeq] at h1
    have h2 := DCPAux.hhat_convex P hP xinf j0 hxS hwS ht.1.le ht.2.le
    have h3 := DCPAux.hhat_convex P hP xinf j0 hyS hxhS hτ.1.le hτ.2
    have h4 : hh xinf ≤ hh w := by
      have : hh ((1 - t) • xinf + t • w) ≤ (1 - t) * hh xinf + t * hh w := h2
      have ht0 := ht.1
      nlinarith
    have : hh w ≤ (1 - τ) * hh y + τ * hh xhat := h3
    linarith
  -- let `τ ↓ 0`
  have hlimτ : Tendsto (fun τ : ℝ => (1 - τ) * hh y + τ * hh xhat) (𝓝[>] 0)
      (𝓝 ((1 - 0) * hh y + 0 * hh xhat)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).tendsto 0
  simp only [sub_zero, one_mul, zero_mul, add_zero] at hlimτ
  apply ge_of_tendsto hlimτ
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ≤ 1 :=
    ((ge_mem_nhds one_pos)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with τ h1 h0
  exact hτ τ ⟨h0, h1⟩
