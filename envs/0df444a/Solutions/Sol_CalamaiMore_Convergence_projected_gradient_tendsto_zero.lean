-- Prove2me | solution 1 for CalamaiMore.Convergence.projected_gradient_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:50:13.607967+00:00
-- url     : https://prove2.me/submissions/589457be-19c8-4a8d-afdb-59b3f2485dec

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

set_option autoImplicit false

open CalamaiMore.Convergence in
theorem p2med4d_proj_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω)
    (hΩcv : Convex ℝ Ω) (y : E) :
    proj Ω y ∈ Ω ∧ ∀ z ∈ Ω, inner ℝ (y - proj Ω y) (z - proj Ω y) ≤ 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hK : IsComplete Ω := hΩc.isComplete
  obtain ⟨v, hv, hvinf⟩ := exists_norm_eq_iInf_of_complete_convex hΩne hK hΩcv y
  have : Nonempty Ω := hΩne.to_subtype
  have hbdd : BddBelow (Set.range fun w : Ω => ‖y - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hex : ∃ z ∈ Ω, ∀ w ∈ Ω, ‖z - y‖ ≤ ‖w - y‖ := by
    refine ⟨v, hv, fun w hw => ?_⟩
    rw [norm_sub_rev v y, norm_sub_rev w y, hvinf]
    exact ciInf_le hbdd ⟨w, hw⟩
  have hP : proj Ω y = Classical.choose hex := by
    unfold proj nearestPoint
    rw [dif_pos hex]
  obtain ⟨hPmem, hPmin⟩ := Classical.choose_spec hex
  rw [hP]
  refine ⟨hPmem, ?_⟩
  have heq : ‖y - Classical.choose hex‖ = ⨅ w : Ω, ‖y - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      rw [norm_sub_rev, norm_sub_rev y]
      exact hPmin w w.2
    · exact ciInf_le hbdd ⟨_, hPmem⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hΩcv hPmem).1 heq

open CalamaiMore.Convergence in
theorem p2med4d_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω)
    (hΩcv : Convex ℝ Ω) (x g : E) (hx : x ∈ Ω) (s : ℝ) :
    ‖proj Ω (x - s • g) - x‖ ^ 2 ≤ -(s * inner ℝ g (proj Ω (x - s • g) - x)) := by
  have h := (p2med4d_proj_spec Ω hΩne hΩc hΩcv (x - s • g)).2 x hx
  set P := proj Ω (x - s • g) with hP
  have e1 : x - s • g - P = -((P - x) + s • g) := by abel
  have e2 : x - P = -(P - x) := by abel
  rw [e1, e2, inner_neg_neg, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h
  linarith

open CalamaiMore.Convergence in
theorem p2med4d_path_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω)
    (hΩcv : Convex ℝ Ω) (x g : E) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    t * ‖proj Ω (x - s • g) - x‖ ^ 2 + s * ‖proj Ω (x - t • g) - x‖ ^ 2
      ≤ (s + t) * inner ℝ (proj Ω (x - s • g) - x) (proj Ω (x - t • g) - x) := by
  obtain ⟨hPs, hVs⟩ := p2med4d_proj_spec Ω hΩne hΩc hΩcv (x - s • g)
  obtain ⟨hPt, hVt⟩ := p2med4d_proj_spec Ω hΩne hΩc hΩcv (x - t • g)
  have h1 := hVs _ hPt
  have h2 := hVt _ hPs
  set P := proj Ω (x - s • g) with hP
  set Q := proj Ω (x - t • g) with hQ
  have e1 : x - s • g - P = -((P - x) + s • g) := by abel
  have e2 : Q - P = (Q - x) - (P - x) := by abel
  have e3 : x - t • g - Q = -((Q - x) + t • g) := by abel
  have e4 : P - Q = (P - x) - (Q - x) := by abel
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  obtain ⟨u, hu⟩ : ∃ u, u = P - x := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = Q - x := ⟨_, rfl⟩
  rw [← hu, ← hv] at h1 h2 ⊢
  simp only [inner_neg_left, inner_add_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h1 h2
  rw [real_inner_comm u v] at h2
  nlinarith [mul_le_mul_of_nonneg_left h1 ht.le, mul_le_mul_of_nonneg_left h2 hs.le]

theorem p2med4d_mono_aux (a b s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) (hst : s ≤ t)
    (h : t * a ^ 2 + s * b ^ 2 ≤ (s + t) * (a * b)) : a ≤ b ∧ s * b ≤ t * a := by
  have key : (t * a - s * b) * (a - b) ≤ 0 := by nlinarith
  have hab : a ≤ b := by
    by_contra hc
    push Not at hc
    have h1 : 0 < t * a - s * b := by
      nlinarith [mul_le_mul_of_nonneg_right hst ha, mul_pos hs (sub_pos.2 hc)]
    have := mul_pos h1 (sub_pos.2 hc)
    linarith
  refine ⟨hab, ?_⟩
  by_contra hc
  push Not at hc
  have h1 : t * a - s * b < 0 := by linarith
  have h2 : 0 ≤ a - b := by
    by_contra h3
    push Not at h3
    have := mul_pos_of_neg_of_neg h1 h3
    linarith
  have hab' : a = b := le_antisymm hab (by linarith)
  subst hab'
  nlinarith [mul_le_mul_of_nonneg_right hst ha]

theorem p2med4d_compare (a b α β γ₂ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ₂) (hγβ : γ₂ * β ≤ α)
    (h : α * a ^ 2 + β * b ^ 2 ≤ (β + α) * (a * b)) :
    a ≤ (1 + γ₂⁻¹) * b ∧ b * β ≤ (1 + γ₂⁻¹) * (a * α) := by
  have hc : 0 < γ₂⁻¹ := inv_pos.2 hγ
  have hcc : γ₂ * γ₂⁻¹ = 1 := mul_inv_cancel₀ hγ.ne'
  rcases le_or_gt β α with hle | hlt
  · obtain ⟨h1, h2⟩ := p2med4d_mono_aux a b β α ha hb hβ hle h
    constructor
    · nlinarith [mul_nonneg hc.le hb]
    · nlinarith [mul_nonneg hc.le (mul_nonneg ha hα.le)]
  · have h' : β * b ^ 2 + α * a ^ 2 ≤ (α + β) * (b * a) := by nlinarith
    obtain ⟨h1, h2⟩ := p2med4d_mono_aux b a α β hb ha hα hlt.le h'
    -- h1 : b ≤ a, h2 : α * a ≤ β * b
    have k1 : γ₂ * a ≤ b := by
      have : α * (γ₂ * a) ≤ α * b := by nlinarith [mul_le_mul_of_nonneg_left h2 hγ.le]
      exact le_of_mul_le_mul_left this hα
    have k2 : γ₂ * (b * β) ≤ a * α := by nlinarith [mul_le_mul_of_nonneg_left hγβ hb]
    constructor
    · have : a = γ₂⁻¹ * (γ₂ * a) := by field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left k1 hc.le, mul_nonneg hc.le hb]
    · have : b * β = γ₂⁻¹ * (γ₂ * (b * β)) := by field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left k2 hc.le, mul_nonneg ha hα.le]

theorem p2med4d_mvt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hΩcv : Convex ℝ Ω) (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x)
    (x y : E) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ c ∈ Set.Ioo (0:ℝ) 1, f y - f x = inner ℝ (gradient f (x + c • (y - x))) (y - x) := by
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ Ω :=
    fun t ht => hΩcv.add_smul_sub_mem hx hy ht
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (inner ℝ (gradient f (x + t • (y - x))) (y - x)) t := by
    intro t ht
    have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hf := (hfd _ (hmem t ht)).hasFDerivAt
    have := hf.comp_hasDerivAt t hline
    have heq : inner ℝ (gradient f (x + t • (y - x))) (y - x)
        = fderiv ℝ f (x + t • (y - x)) (y - x) := InnerProductSpace.toDual_symm_apply
    rw [heq]
    exact this
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (x + t • (y - x)))
    (fun t => inner ℝ (gradient f (x + t • (y - x))) (y - x)) zero_lt_one
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
  refine ⟨c, hc, ?_⟩
  rw [hceq]
  simp

open CalamaiMore.Convergence in
theorem p2med4d_projGrad_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (Ω : Set E) (y : E) (hy : y ∈ Ω) (n : E)
    (hn : ∀ z ∈ Ω, inner ℝ n (z - y) ≤ 0) :
    ‖projGrad f Ω y‖ ≤ 2 * ‖gradient f y + n‖ := by
  have hT0 : (0 : E) ∈ CalamaiMore.Shared.tangentCone Ω y := by
    apply subset_closure
    show ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + τ • (0:E) ∈ Ω
    exact Filter.Eventually.of_forall (fun τ => by simpa using hy)
  have hTn : ∀ v ∈ CalamaiMore.Shared.tangentCone Ω y, inner ℝ n v ≤ 0 := by
    intro v hv
    have hclosed : IsClosed {v : E | inner ℝ n v ≤ 0} :=
      isClosed_le (continuous_const.inner continuous_id) continuous_const
    have hsub : CalamaiMore.Shared.feasibleDirections Ω y ⊆ {v : E | inner ℝ n v ≤ 0} := by
      intro w hw
      have hw' : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + τ • w ∈ Ω := hw
      have hpos : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0:ℝ) < τ := self_mem_nhdsWithin
      obtain ⟨τ, hτ1, hτ2⟩ := (hw'.and hpos).exists
      have h3 := hn _ hτ1
      simp only [add_sub_cancel_left, real_inner_smul_right] at h3
      show inner ℝ n w ≤ 0
      by_contra hc
      push Not at hc
      have := mul_pos hτ2 hc
      linarith
    exact closure_minimal hsub hclosed hv
  unfold projGrad nearestPoint
  split_ifs with h
  · obtain ⟨hpT, hpmin⟩ := Classical.choose_spec h
    set p := Classical.choose h
    set g := gradient f y
    have h1 := hpmin 0 hT0
    simp only [sub_neg_eq_add, zero_add] at h1
    have h2 : ‖p + g‖ ^ 2 ≤ ‖g‖ ^ 2 := by gcongr
    rw [norm_add_sq_real] at h2
    have h3 := hTn p hpT
    have h4 : inner ℝ (-(g + n)) p ≤ ‖g + n‖ * ‖p‖ := by
      calc _ ≤ ‖-(g + n)‖ * ‖p‖ := real_inner_le_norm _ _
        _ = _ := by rw [norm_neg]
    have h5 : inner ℝ (-(g + n)) p = - inner ℝ p g - inner ℝ n p := by
      rw [inner_neg_left, inner_add_left, real_inner_comm g p]; ring
    have h6 : ‖p‖ ^ 2 ≤ 2 * ‖g + n‖ * ‖p‖ := by nlinarith
    have hp0 := norm_nonneg p
    have hgn := norm_nonneg (g + n)
    nlinarith
  · simp

open CalamaiMore.Convergence in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (γ₃ : ℝ) (hα₃ : ∀ k, α k ≤ γ₃)
    (hbdd : BddBelow (f '' Ω)) (huc : UniformContinuousOn (gradient f) Ω) :
    Filter.Tendsto (fun k => ‖projGrad f Ω (x k)‖) Filter.atTop (nhds 0) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨hx0, hstep⟩ := hrun
  have hxs : ∀ k, x (k + 1) = proj Ω (x k - α k • gradient f (x k)) := fun k => (hstep k).2.1
  have hxΩ : ∀ k, x k ∈ Ω := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k _ =>
      rw [hxs k]
      exact (p2med4d_proj_spec Ω hΩne hΩc hΩcv _).1
  have hαpos : ∀ k, 0 < α k := fun k => (hstep k).1
  have hμ1 := hμ₁.1
  have hμ2 := hμ₂.2
  -- sufficient decrease
  have hkey : ∀ k, μ₁ * ‖x (k + 1) - x k‖ ^ 2 ≤ α k * (f (x k) - f (x (k + 1))) ∧
      0 ≤ f (x k) - f (x (k + 1)) := by
    intro k
    have h21 := (hstep k).2.2.1
    have hd := p2med4d_descent Ω hΩne hΩc hΩcv (x k) (gradient f (x k)) (hxΩ k) (α k)
    rw [← hxs k] at hd
    have ha := hαpos k
    set I := inner ℝ (gradient f (x k)) (x (k + 1) - x k)
    have hI : 0 ≤ -I := by
      by_contra hc
      push Not at hc
      have : α k * (-I) < 0 := mul_neg_of_pos_of_neg ha hc
      have h0 := sq_nonneg ‖x (k + 1) - x k‖
      linarith
    constructor
    · have e1 := mul_le_mul_of_nonneg_left hd hμ1.le
      have e2 := mul_le_mul_of_nonneg_left h21 ha.le
      linarith
    · have e1 := mul_nonneg hμ1.le hI
      linarith
  -- convergence of the function values
  have hanti : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    linarith [(hkey k).2]
  obtain ⟨m, hm⟩ := hbdd
  have hbddr : BddBelow (Set.range fun k => f (x k)) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hm ⟨x k, hxΩ k, rfl⟩
  have hlim := tendsto_atTop_ciInf hanti hbddr
  have he : Filter.Tendsto (fun k => f (x k) - f (x (k + 1))) Filter.atTop (nhds 0) := by
    have := hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
    simpa using this
  have hγ₃ : 0 < γ₃ := lt_of_lt_of_le (hαpos 0) (hα₃ 0)
  -- steps go to zero
  have hdn : Filter.Tendsto (fun k => ‖x (k + 1) - x k‖) Filter.atTop (nhds 0) := by
    have hle : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ γ₃ / μ₁ * (f (x k) - f (x (k + 1))) := by
      intro k
      obtain ⟨h1, h2⟩ := hkey k
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ1]
      have e1 := mul_le_mul_of_nonneg_right (hα₃ k) h2
      linarith
    have hsq : Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ ^ 2) Filter.atTop (nhds 0) := by
      apply squeeze_zero (fun k => by positivity) hle
      simpa using he.const_mul (γ₃ / μ₁)
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  -- ratio goes to zero
  have hr : Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ / α k) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set c₀ : ℝ := 1 + γ₂⁻¹ with hc₀
    have hc₀pos : 0 < c₀ := by positivity
    set η : ℝ := ε * (1 - μ₂) / c₀ with hη
    have hηpos : 0 < η := by
      have : 0 < 1 - μ₂ := by linarith
      positivity
    obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1 huc η hηpos
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hdn (δ / c₀) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 he (μ₁ * γ₁ * ε ^ 2) (by positivity)
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    have hk1 := hN₁ k (le_of_max_le_left hk)
    have hk2 := hN₂ k (le_of_max_le_right hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hk1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hkey k).2] at hk2
    have ha := hαpos k
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ ha]
    obtain ⟨hk3, hk4⟩ := hkey k
    set b := ‖x (k + 1) - x k‖ with hb
    have hb0 : 0 ≤ b := norm_nonneg _
    rcases (hstep k).2.2.2 with h1 | ⟨β, hβpos, hβle, h23⟩
    · -- long step
      have : b ^ 2 < (ε * α k) ^ 2 := by
        have e1 : μ₁ * b ^ 2 < μ₁ * (ε * α k) ^ 2 := by
          calc μ₁ * b ^ 2 ≤ α k * (f (x k) - f (x (k + 1))) := hk3
            _ < α k * (μ₁ * γ₁ * ε ^ 2) := mul_lt_mul_of_pos_left hk2 ha
            _ ≤ α k * (μ₁ * α k * ε ^ 2) := by
                apply mul_le_mul_of_nonneg_left _ ha.le
                have : μ₁ * γ₁ ≤ μ₁ * α k := mul_le_mul_of_nonneg_left h1 hμ1.le
                exact mul_le_mul_of_nonneg_right this (sq_nonneg ε)
            _ = μ₁ * (ε * α k) ^ 2 := by ring
        exact lt_of_mul_lt_mul_left e1 hμ1.le
      have hεα : 0 ≤ ε * α k := by positivity
      exact lt_of_pow_lt_pow_left₀ 2 hεα this
    · -- short step with a rejected trial step
      have hβ : 0 < β := pos_of_mul_pos_right hβpos hγ₂.le
      set y := projPath f Ω (x k) β with hy
      have hyeq : y = proj Ω (x k - β • gradient f (x k)) := rfl
      have hyΩ : y ∈ Ω := by rw [hyeq]; exact (p2med4d_proj_spec Ω hΩne hΩc hΩcv _).1
      set u := y - x k with hu
      set a := ‖u‖ with ha_def
      have ha0 : 0 ≤ a := norm_nonneg _
      have hdescβ : a ^ 2 ≤ -(β * inner ℝ (gradient f (x k)) u) := by
        have := p2med4d_descent Ω hΩne hΩc hΩcv (x k) (gradient f (x k)) (hxΩ k) β
        rw [← hyeq] at this
        exact this
      have hpath := p2med4d_path_ineq Ω hΩne hΩc hΩcv (x k) (gradient f (x k)) β (α k) hβ ha
      rw [← hyeq, ← hxs k] at hpath
      have hcs : inner ℝ u (x (k + 1) - x k) ≤ a * b := real_inner_le_norm _ _
      have hpath' : α k * a ^ 2 + β * b ^ 2 ≤ (β + α k) * (a * b) := by
        have := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ β + α k)
        linarith
      obtain ⟨hcmp1, hcmp2⟩ := p2med4d_compare a b (α k) β γ₂ ha0 hb0 ha hβ hγ₂ hβle hpath'
      obtain ⟨c, hc, hmvt⟩ := p2med4d_mvt Ω hΩcv f hfd (x k) y (hxΩ k) hyΩ
      have hξΩ : x k + c • u ∈ Ω := hΩcv.add_smul_sub_mem (hxΩ k) hyΩ ⟨hc.1.le, hc.2.le⟩
      have hdist : dist (x k + c • u) (x k) < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hc.1]
        calc c * a ≤ a := mul_le_of_le_one_left ha0 hc.2.le
          _ ≤ c₀ * b := hcmp1
          _ < c₀ * (δ / c₀) := mul_lt_mul_of_pos_left hk1 hc₀pos
          _ = δ := by field_simp
      have hG := hUC _ hξΩ _ (hxΩ k) hdist
      rw [dist_eq_norm] at hG
      set G := gradient f (x k + c • u) - gradient f (x k) with hGdef
      have hGle : inner ℝ G u ≤ η * a := by
        calc inner ℝ G u ≤ ‖G‖ * a := real_inner_le_norm _ _
          _ ≤ η * a := mul_le_mul_of_nonneg_right hG.le ha0
      have hGexp : inner ℝ G u = inner ℝ (gradient f (x k + c • u)) u
          - inner ℝ (gradient f (x k)) u := by
        rw [hGdef, inner_sub_left]
      -- the Armijo test failed at β
      have h23' : μ₂ * inner ℝ (gradient f (x k)) u < inner ℝ (gradient f (x k + c • u)) u := by
        have : f y - f (x k) = inner ℝ (gradient f (x k + c • u)) u := hmvt
        linarith
      set J := inner ℝ (gradient f (x k)) u with hJ
      -- (1 - μ₂) (-J) < η a
      have hstrict : (1 - μ₂) * (-J) < η * a := by linarith
      have hμ2' : 0 < 1 - μ₂ := by linarith
      have hA : (1 - μ₂) * a ^ 2 < β * η * a := by
        calc (1 - μ₂) * a ^ 2 ≤ (1 - μ₂) * (-(β * J)) := mul_le_mul_of_nonneg_left hdescβ hμ2'.le
          _ = β * ((1 - μ₂) * (-J)) := by ring
          _ < β * (η * a) := mul_lt_mul_of_pos_left hstrict hβ
          _ = β * η * a := by ring
      have hapos : 0 < a := by
        by_contra hc'
        have : a = 0 := le_antisymm (not_lt.1 hc') ha0
        rw [this] at hA
        simp at hA
      have hB : (1 - μ₂) * a < β * η := by
        have : a * ((1 - μ₂) * a) < a * (β * η) := by
          calc a * ((1 - μ₂) * a) = (1 - μ₂) * a ^ 2 := by ring
            _ < β * η * a := hA
            _ = a * (β * η) := by ring
        exact lt_of_mul_lt_mul_left this ha0
      -- combine
      have hC : (1 - μ₂) * (b * β) < (β * (1 - μ₂)) * (ε * α k) := by
        calc (1 - μ₂) * (b * β) ≤ (1 - μ₂) * (c₀ * (a * α k)) :=
              mul_le_mul_of_nonneg_left hcmp2 hμ2'.le
          _ = c₀ * α k * ((1 - μ₂) * a) := by ring
          _ < c₀ * α k * (β * η) := mul_lt_mul_of_pos_left hB (by positivity)
          _ = (β * (1 - μ₂)) * (ε * α k) := by rw [hη]; field_simp
      have hC' : (β * (1 - μ₂)) * b < (β * (1 - μ₂)) * (ε * α k) := by
        calc (β * (1 - μ₂)) * b = (1 - μ₂) * (b * β) := by ring
          _ < _ := hC
      exact lt_of_mul_lt_mul_left hC' (by positivity)
  -- gradient differences go to zero
  have hgd : Filter.Tendsto (fun k => ‖gradient f (x (k + 1)) - gradient f (x k)‖)
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdn δ hδ
    refine ⟨N, fun k hk => ?_⟩
    have h1 := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have := hUC _ (hxΩ (k + 1)) _ (hxΩ k) (by rw [dist_eq_norm]; exact h1)
    rwa [dist_eq_norm] at this
  -- bound on the projected gradient at the next iterate
  have hpg : ∀ k, ‖projGrad f Ω (x (k + 1))‖ ≤
      2 * (‖gradient f (x (k + 1)) - gradient f (x k)‖ + ‖x (k + 1) - x k‖ / α k) := by
    intro k
    have ha := hαpos k
    set n : E := (α k)⁻¹ • (x k - α k • gradient f (x k) - x (k + 1)) with hn
    have hnn : ∀ z ∈ Ω, inner ℝ n (z - x (k + 1)) ≤ 0 := by
      intro z hz
      rw [hn, real_inner_smul_left]
      have h := (p2med4d_proj_spec Ω hΩne hΩc hΩcv (x k - α k • gradient f (x k))).2 z hz
      rw [← hxs k] at h
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ha.le) h
    have hb := p2med4d_projGrad_le f Ω (x (k + 1)) (hxΩ (k + 1)) n hnn
    have hsum : gradient f (x (k + 1)) + n
        = (gradient f (x (k + 1)) - gradient f (x k)) + (α k)⁻¹ • (x k - x (k + 1)) := by
      rw [hn]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
      abel
    rw [hsum] at hb
    have htri := norm_add_le (gradient f (x (k + 1)) - gradient f (x k))
      ((α k)⁻¹ • (x k - x (k + 1)))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha), norm_sub_rev (x k) (x (k + 1)),
      ← div_eq_inv_mul] at htri
    linarith
  have hlim1 : Filter.Tendsto (fun k => ‖projGrad f Ω (x (k + 1))‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun k => norm_nonneg _) hpg
    simpa using (hgd.add hr).const_mul 2
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hlim1
