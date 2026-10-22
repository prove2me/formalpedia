-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.variance_reduced_progress_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:50:41.327746+00:00
-- url     : https://prove2.me/submissions/621eb684-460d-4ee4-aac6-8baed9e4999a

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction



namespace FirstOrderOpt.FiniteSum

open Set Filter Topology FirstOrderOpt.Prox

/-- directional derivative nonnegativity -/
lemma dir_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E →L[ℝ] ℝ} {X : Set E} (hX : Convex ℝ X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hd : HasFDerivWithinAt F F' X a) {c : ℝ}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ s * c + (F (a + s • (b - a)) - F a)) :
    0 ≤ c + F' (b - a) := by
  have h1 : HasDerivWithinAt (fun s : ℝ => a + s • (b - a)) (b - a) (Icc 0 1) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a).hasDerivWithinAt (s := Icc (0:ℝ) 1)
    simpa using this
  have hmaps : MapsTo (fun s : ℝ => a + s • (b - a)) (Icc 0 1) X := by
    intro s hs
    exact hX.add_smul_sub_mem ha hb hs
  have h2 : HasDerivWithinAt (F ∘ fun s : ℝ => a + s • (b - a)) (F' (b - a)) (Icc 0 1) 0 := by
    exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := F) (f := fun s : ℝ => a + s • (b - a)) 0
      (by simpa using hd) h1 hmaps
  rw [hasDerivWithinAt_iff_tendsto_slope] at h2
  have hset : Icc (0:ℝ) 1 \ {0} = Ioc 0 1 := by
    ext s; simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨h0, h1⟩, hne⟩; exact ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1⟩, h0.ne'⟩
  rw [hset] at h2
  have h3 : Tendsto (slope (F ∘ fun s : ℝ => a + s • (b - a)) 0) (𝓝[Ioo 0 1] 0) (𝓝 (F' (b - a))) :=
    h2.mono_left (nhdsWithin_mono _ Ioo_subset_Ioc_self)
  have : (𝓝[Ioo (0:ℝ) 1] 0).NeBot := left_nhdsWithin_Ioo_neBot (a := (0:ℝ)) (b := 1) (by norm_num)
  have h4 : -c ≤ F' (b - a) := by
    refine ge_of_tendsto h3 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs.1
    have := h s hs0 hs.2.le
    rw [slope_def_field]
    simp only [Function.comp, sub_zero, zero_smul, add_zero]
    rw [le_div_iff₀ hs0]
    nlinarith
  linarith


lemma line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E → E →L[ℝ] ℝ} (hF : ∀ x, HasFDerivAt F (F' x) x) (x d : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F (x + t • d)) (F' (x + s • d) d) s := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  exact (hF (x + s • d)).comp_hasDerivAt s h1

/-- descent lemma -/
lemma descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (F' : E → E →L[ℝ] ℝ) (hF : ∀ x, HasFDerivAt F (F' x) x) (L : ℝ)
    (hs : ∀ x y, ‖F' x - F' y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + F' x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let k : ℝ → ℝ := fun t => F (x + t • d) - F x - t * F' x d - L * t ^ 2 * ‖d‖ ^ 2 / 2
  have hk : ∀ t, HasDerivAt k (F' (x + t • d) d - F' x d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := line_hasDerivAt hF x d t
    have h2 : HasDerivAt (fun t : ℝ => t * F' x d) (F' x d) t := by
      simpa using (hasDerivAt_id t).mul_const (F' x d)
    have h3 : HasDerivAt (fun t : ℝ => L * t ^ 2 * ‖d‖ ^ 2 / 2) (L * t * ‖d‖ ^ 2) t := by
      have := (((hasDerivAt_id t).pow 2).const_mul L).mul_const (‖d‖ ^ 2) |>.div_const 2
      exact this.congr_deriv (by simp only [id]; push_cast; ring)
    exact ((h1.sub_const (F x)).sub h2).sub h3
  have hanti : AntitoneOn k (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t _ => (hk t).continuousAt.continuousWithinAt
    · exact fun t _ => (hk t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0:ℝ) < t := ht
      rw [(hk t).deriv]
      have h1 : F' (x + t • d) d - F' x d ≤ ‖F' (x + t • d) - F' x‖ * ‖d‖ := by
        have := (F' (x + t • d) - F' x).le_opNorm d
        have h' : |F' (x + t • d) d - F' x d| ≤ ‖F' (x + t • d) - F' x‖ * ‖d‖ := by
          simpa [Real.norm_eq_abs] using this
        exact le_trans (le_abs_self _) h'
      have h2 : ‖F' (x + t • d) - F' x‖ ≤ L * (t * ‖d‖) := by
        have := hs (x + t • d) x
        simpa [norm_smul, abs_of_pos ht0] using this
      have h3 : ‖F' (x + t • d) - F' x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      nlinarith
  have := hanti (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 (zero_le_one' ℝ)) zero_le_one
  simp only [k] at this
  simp at this
  have e : x + d = y := by simp [hd]
  rw [e] at this
  linarith



theorem vrp_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgrad : ∀ x, HasFDerivAt f (gradf_full x) x)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X, f y ≥ f x + (gradf_full x) (y - x) + μ * ν.V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + ν.V xt xt1 ≤ γ * (Gt y) + γ * h y + ν.V xt y) :
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + ν.V xt1 x ≤
      (1 - γ * μ) * ν.V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2 := by
  intro x hx
  set u := x - xt1 with hu
  set v := xt1 - xt with hv
  have hxv : x - xt = u + v := by simp [hu, hv]
  -- three point
  have hdir := dir_nonneg hXconv hxt1 hx (ν.hasFDerivWithinAt xt1 hxt1) (F := ν.ω)
    (c := γ * Gt u + γ * (h x - h xt1) - ν.dω xt u) (by
    intro s hs0 hs1
    have hy : xt1 + s • (x - xt1) ∈ X := hXconv.add_smul_sub_mem hxt1 hx ⟨hs0.le, hs1⟩
    have h1 := hmin _ hy
    have h2 := hhconv.2 hxt1 hx (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring)
    have e : (1 - s) • xt1 + s • x = xt1 + s • (x - xt1) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at h2
    simp only [smul_eq_mul] at h2
    have e2 : xt1 + s • (x - xt1) - xt = v + s • u := by simp only [hu, hv]; abel
    have hVy : ν.V xt (xt1 + s • (x - xt1)) = ν.ω (xt1 + s • (x - xt1)) - ν.ω xt
        - (ν.dω xt v + s * ν.dω xt u) := by
      unfold DistanceGeneratingFunction.V
      rw [e2]; simp
    have hV1 : ν.V xt xt1 = ν.ω xt1 - ν.ω xt - ν.dω xt v := by
      unfold DistanceGeneratingFunction.V; rfl
    have hGy : Gt (xt1 + s • (x - xt1)) = Gt xt1 + s * Gt u := by simp [hu]
    rw [hVy, hV1, hGy] at h1
    nlinarith)
  have hV1 : ν.V xt xt1 = ν.ω xt1 - ν.ω xt - ν.dω xt v := by
    unfold DistanceGeneratingFunction.V; rfl
  have hV2 : ν.V xt1 x = ν.ω x - ν.ω xt1 - ν.dω xt1 u := by
    unfold DistanceGeneratingFunction.V; rfl
  have hV3 : ν.V xt x = ν.ω x - ν.ω xt - (ν.dω xt u + ν.dω xt v) := by
    unfold DistanceGeneratingFunction.V; rw [hxv, map_add]
  have hGu : Gt u = Gt x - Gt xt1 := by simp [hu]
  have TP : γ * Gt xt1 + γ * h xt1 + ν.V xt xt1 + ν.V xt1 x ≤
      γ * Gt x + γ * h x + ν.V xt x := by
    rw [hV1, hV2, hV3]
    rw [hGu] at hdir
    nlinarith
  -- smoothness
  have hdesc := descent f gradf_full hgrad L hsmooth xt xt1
  have hs := hstrong xt hxt x hx
  have hVge : (1 / 2) * ‖v‖ ^ 2 ≤ ν.V xt xt1 := by
    have := ν.strongConvex xt hxt xt1 hxt1
    unfold DistanceGeneratingFunction.V; linarith
  have hG : ∀ w, Gt w = δt w + gradf_full xt w := by intro w; simp [hδt]
  have hδv : |δt v| ≤ ‖δt‖ * ‖v‖ := by
    have := δt.le_opNorm v
    simpa [Real.norm_eq_abs] using this
  have hxv' : gradf_full xt (x - xt) = gradf_full xt u + gradf_full xt v := by rw [hxv, map_add]
  have hδxv : δt (x - xt) = δt u + δt v := by rw [hxv, map_add]
  have hGuv : Gt x - Gt xt1 = Gt u := hGu.symm
  have hnonneg : 0 ≤ ‖v‖ := norm_nonneg _
  have hD : 0 ≤ ‖δt‖ := norm_nonneg _
  have hq1 : γ * L * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 / 2 := by nlinarith [sq_nonneg ‖v‖]
  have hq2 := sq_nonneg (‖v‖ / 2 - γ * ‖δt‖)
  have m1 := mul_le_mul_of_nonneg_left hdesc hγ.le
  have m2 := mul_le_mul_of_nonneg_left hs hγ.le
  have m3 := mul_le_mul_of_nonneg_left hδv hγ.le
  have hxt1x : xt1 - xt = v := rfl
  have hGt1 : Gt xt1 = δt xt1 + gradf_full xt xt1 := hG _
  have hΔ : gradf_full xt (xt1 - xt) = gradf_full xt v := rfl
  have hδu : δt u = δt (x - xt) - δt v := by rw [hδxv]; ring
  have hgu : gradf_full xt u = gradf_full xt (x - xt) - gradf_full xt v := by rw [hxv']; ring
  have hGu2 : Gt u = δt u + gradf_full xt u := hG _
  rw [hΨ, hΨ]
  have habs := neg_abs_le (δt v)
  nlinarith [abs_nonneg (δt v), le_abs_self (δt v)]

end FirstOrderOpt.FiniteSum

open FirstOrderOpt.FiniteSum
open FirstOrderOpt.Prox

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgrad : ∀ x, HasFDerivAt f (gradf_full x) x)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X, f y ≥ f x + (gradf_full x) (y - x) + μ * ν.V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + ν.V xt xt1 ≤ γ * (Gt y) + γ * h y + ν.V xt y) :
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + ν.V xt1 x ≤
      (1 - γ * μ) * ν.V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2 := by
  exact vrp_core X hXconv hXclosed ν f h Ψ hΨ hhconv gradf_full hgrad L hL hsmooth μ hμ hstrong γ hγ hLγ xt xt1 hxt hxt1 Gt δt hδt hmin
