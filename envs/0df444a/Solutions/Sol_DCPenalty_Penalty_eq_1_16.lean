-- Prove2me | solution 1 for DCPenalty.Penalty.eq_1_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:34:50.933978+00:00
-- url     : https://prove2.me/submissions/070bce35-b72c-4840-b33b-e998831aaf63

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

end DCPAux

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

namespace DCPAux

/-- Danskin's formula for a finite max of functions differentiable at `x`. -/
lemma danskin_finite {n N : ℕ} (hN : 0 < N) (g : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (hg : ∀ j, DifferentiableAt ℝ (g j) x) :
    ∃ c, HasOneSidedDirDeriv
        (fun y => Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => g j y)) x d c ∧
      IsGreatest ((fun j => fderiv ℝ (g j) x d) ''
        {j | Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => g j x) = g j x}) c := by
  set M : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => g j y) with hM
  set A : Set (Fin N) := {j | M x = g j x} with hA
  have hAne : A.Nonempty := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (⟨⟨0, hN⟩, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin N)).Nonempty) (fun j => g j x)
    exact ⟨j, hj⟩
  -- the image is finite and nonempty, so it has a greatest element
  have hfin : ((fun j => fderiv ℝ (g j) x d) '' A).Finite := (Set.toFinite A).image _
  have hne : ((fun j => fderiv ℝ (g j) x d) '' A).Nonempty := hAne.image _
  obtain ⟨c, hcmem, hcmax⟩ : ∃ c ∈ ((fun j => fderiv ℝ (g j) x d) '' A),
      ∀ b ∈ ((fun j => fderiv ℝ (g j) x d) '' A), b ≤ c := by
    obtain ⟨c, hc⟩ := hfin.exists_maximalFor id _ hne
    refine ⟨c, hc.1, fun b hb => ?_⟩
    rcases le_total b c with h | h
    · exact h
    · exact hc.2 hb h
  refine ⟨c, ?_, ⟨hcmem, fun b hb => hcmax b hb⟩⟩
  obtain ⟨jstar, hjA, rfl⟩ := hcmem
  have hq : ∀ j, Tendsto (fun δ : ℝ => (g j (x + δ • d) - g j x) / δ) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (g j) x d)) := fun j => dirDeriv_of_differentiableAt (hg j) d
  have hcont : ∀ j, Tendsto (fun δ : ℝ => g j (x + δ • d)) (𝓝[>] 0) (𝓝 (g j x)) := by
    intro j
    have h1 : Tendsto (fun δ : ℝ => x + δ • d) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun δ : ℝ => x + δ • d) := by fun_prop
      simpa using this.tendsto 0
    exact ((hg j).continuousAt.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  -- eventually, every inactive piece is strictly below `g jstar`
  have hinact : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ j, j ∉ A → g j (x + δ • d) < g jstar (x + δ • d) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j ∈ A
    · exact Eventually.of_forall (fun _ h => absurd hj h)
    · have hlt : g j x < g jstar x := by
        have h1 : g j x ≤ M x := Finset.le_sup' (fun j => g j x) (Finset.mem_univ j)
        have h2 : M x = g jstar x := hjA
        have h3 : g j x ≠ M x := fun h => hj h.symm
        exact lt_of_le_of_ne (h2 ▸ h1) (h2 ▸ h3)
      have := (hcont j).sub (hcont jstar)
      have hev := this.eventually (gt_mem_nhds (sub_neg.2 hlt))
      filter_upwards [hev] with δ hδ _
      linarith
  have hpos : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  unfold HasOneSidedDirDeriv
  rw [tendsto_order]
  constructor
  · intro a ha
    have hev := (hq jstar).eventually (lt_mem_nhds ha)
    filter_upwards [hev, hpos] with δ hδ hδp
    have h1 : g jstar (x + δ • d) ≤ M (x + δ • d) :=
      Finset.le_sup' (fun j => g j (x + δ • d)) (Finset.mem_univ jstar)
    have h2 : M x = g jstar x := hjA
    calc a < (g jstar (x + δ • d) - g jstar x) / δ := hδ
      _ ≤ (M (x + δ • d) - M x) / δ := by
        rw [h2]; exact div_le_div_of_nonneg_right (by linarith) hδp.le
  · intro a ha
    have hall : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ j, j ∈ A → (g j (x + δ • d) - g j x) / δ < a := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j ∈ A
      · have hle : fderiv ℝ (g j) x d < a :=
          lt_of_le_of_lt (hcmax _ ⟨j, hj, rfl⟩) ha
        filter_upwards [(hq j).eventually (gt_mem_nhds hle)] with δ hδ _
        exact hδ
      · exact Eventually.of_forall (fun _ h => absurd h hj)
    filter_upwards [hall, hinact] with δ hδ hδi
    obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup' (⟨⟨0, hN⟩, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin N)).Nonempty) (fun j => g j (x + δ • d))
    have hj1A : j1 ∈ A := by
      by_contra hcon
      have h1 := hδi j1 hcon
      have h2 : g jstar (x + δ • d) ≤ M (x + δ • d) :=
        Finset.le_sup' (fun j => g j (x + δ • d)) (Finset.mem_univ jstar)
      have h3 : M (x + δ • d) = g j1 (x + δ • d) := hj1
      linarith
    have hMx : M x = g j1 x := hj1A
    have := hδ j1 hj1A
    show (M (x + δ • d) - M x) / δ < a
    rw [hMx, show M (x + δ • d) = g j1 (x + δ • d) from hj1]
    exact this

end DCPAux

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) :
    ∀ x ∈ P.X, ∀ d ∈ tangentConeB P.X x, ∀ i : Fin (m + 1),
      ∃ c, HasOneSidedDirDeriv (P.psi i) x d c ∧
        IsGreatest ((fun j => fderiv ℝ (P.ψ i j) x d) '' (P.Jact i x)) c := by
  intro x hx d _ i
  have hxS : x ∈ P.S := hP.X_subset_S hx
  have hd : ∀ j, DifferentiableAt ℝ (P.ψ i j) x := fun j =>
    ((hP.ψ_C1 i j).differentiableOn one_ne_zero).differentiableAt (hP.isOpen_S.mem_nhds hxS)
  exact DCPAux.danskin_finite (P.J_pos i) (P.ψ i) x d hd
