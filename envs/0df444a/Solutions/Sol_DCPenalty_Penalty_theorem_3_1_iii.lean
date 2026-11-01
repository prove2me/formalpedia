-- Prove2me | solution 1 for DCPenalty.Penalty.theorem_3_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:33:32.840446+00:00
-- url     : https://prove2.me/submissions/69f79077-ebab-4f4a-b476-7b815f9d3e9f

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm
import Theorems.Thm_DCPenalty_Penalty_eq_3_26
import Theorems.Thm_DCPenalty_Penalty_theorem_2_1
import Theorems.Thm_DCPenalty_Penalty_eq_1_16

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

end DCPAux

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {p ε ρ0 σ : ℝ} {η : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : P.IsPenaltyRun p ε ρ0 σ η x)
    {K : ℕ → ℕ} (hK : StrictMono K) {xinf : EuclideanSpace ℝ (Fin n)}
    (hlim : Tendsto (x ∘ K) atTop (𝓝 xinf))
    (hfeas : xinf ∈ P.Ω) (hact : (P.Ieq xinf).Nonempty) (hpscq : P.PSCQ xinf) :
    P.IsBStationary xinf := by
  have hxX : xinf ∈ P.X := hfeas.1
  have hxS : xinf ∈ P.S := hP.X_subset_S hxX
  rw [theorem_2_1 P hP hfeas hact hpscq]
  intro jj hjj d hd
  have hdX : d ∈ tangentConeB P.X xinf :=
    DCPAux.tangentConeB_mono (fun y hy => hy.1) xinf hd
  obtain ⟨cψ, hψ, hgr⟩ := eq_1_16 P hP xinf hxX d hdX 0
  obtain ⟨j0, hj0, hj0eq⟩ := hgr.1
  subst hj0eq
  have h326 := (eq_3_26 P hP hrun hK hlim hfeas hact hpscq jj hjj j0 hj0).2
  obtain ⟨cζ, hζ⟩ := DCPAux.dirDeriv_exists_of_convex hP.isOpen_S (hP.ζ_convex 0) hxS d
  have hφd : DifferentiableAt ℝ (P.φ 0) xinf :=
    ((hP.φ_C1 0).differentiableOn one_ne_zero).differentiableAt (hP.isOpen_S.mem_nhds hxS)
  have hφ := DCPAux.dirDeriv_of_differentiableAt hφd d
  refine ⟨fderiv ℝ (P.φ 0) xinf d + cζ - fderiv ℝ (P.ψ 0 j0) xinf d, ?_, ?_⟩
  · unfold HasOneSidedDirDeriv at hφ hζ hψ ⊢
    refine ((hφ.add hζ).sub hψ).congr ?_
    intro t
    simp only [DCProblem.F]
    ring
  · obtain ⟨xs, τ, hxsY, -, hτpos, hτ, hv⟩ := hd
    set v : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (τ k)⁻¹ • (xs k - xinf) with hvdef
    have hxs_eq : ∀ k, xs k = xinf + τ k • v k := by
      intro k
      simp only [hvdef, smul_smul, mul_inv_cancel₀ (hτpos k).ne', one_smul]
      abel
    obtain ⟨Kz, r, hr, hKz⟩ := DCPAux.lip_ball_of_convex hP.isOpen_S (hP.ζ_convex 0) hxS
    have hz := DCPAux.hadamard hr hKz hζ hτpos hτ hv
    have hlin1 : Tendsto (fun k => fderiv ℝ (P.φ 0) xinf (v k)) atTop
        (𝓝 (fderiv ℝ (P.φ 0) xinf d)) :=
      ((fderiv ℝ (P.φ 0) xinf).continuous.tendsto d).comp hv
    have hlin2 : Tendsto (fun k => fderiv ℝ (P.ψ 0 j0) xinf (v k)) atTop
        (𝓝 (fderiv ℝ (P.ψ 0 j0) xinf d)) :=
      ((fderiv ℝ (P.ψ 0 j0) xinf).continuous.tendsto d).comp hv
    have hquad : Tendsto (fun k => P.L 0 * τ k * ‖v k‖ ^ 2 / 2) atTop (𝓝 0) := by
      have := ((hτ.const_mul (P.L 0)).mul ((hv.norm).pow 2)).div_const 2
      simpa using this
    have hlimq := ((hlin1.add hquad).add hz).sub hlin2
    simp only [add_zero] at hlimq
    apply ge_of_tendsto hlimq
    refine Eventually.of_forall (fun k => ?_)
    have hmin := h326 (xs k) (hxsY k)
    have hpos := hτpos k
    simp only [DCProblem.phiHat, lin, sub_self, map_zero, norm_zero] at hmin
    rw [hxs_eq k] at hmin
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg hpos.le] at hmin
    have key : 0 ≤ (P.ζ 0 (xinf + τ k • v k) - P.ζ 0 xinf) / τ k +
        (fderiv ℝ (P.φ 0) xinf (v k) + P.L 0 * τ k * ‖v k‖ ^ 2 / 2 -
          fderiv ℝ (P.ψ 0 j0) xinf (v k)) := by
      have h2 : 0 ≤ (P.ζ 0 (xinf + τ k • v k) - P.ζ 0 xinf) +
          τ k * (fderiv ℝ (P.φ 0) xinf (v k) + P.L 0 * τ k * ‖v k‖ ^ 2 / 2 -
            fderiv ℝ (P.ψ 0 j0) xinf (v k)) := by
        nlinarith [hmin]
      have h3 := div_nonneg h2 hpos.le
      rw [add_div, mul_div_cancel_left₀ _ hpos.ne'] at h3
      exact h3
    linarith [key]
