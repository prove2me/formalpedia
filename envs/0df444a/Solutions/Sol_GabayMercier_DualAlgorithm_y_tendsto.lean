-- Prove2me | solution 1 for GabayMercier.DualAlgorithm.y_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:53:47.803527+00:00
-- url     : https://prove2.me/submissions/29f31f26-3802-4546-8262-030385d73f73

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

set_option autoImplicit false

namespace GMyT5ddb

/-- Strong convexity inequality from a strongly monotone gradient. -/
theorem strong_cvx {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    {f : Y → ℝ} {f' : Y → Y} {γ : ℝ} (hg : ∀ y, HasGradientAt f (f' y) y)
    (hm : ∀ y z, γ * ‖y - z‖ ^ 2 ≤ inner ℝ (f' y - f' z) (y - z)) (x y : Y) :
    f y + inner ℝ (f' y) (x - y) + γ / 2 * ‖x - y‖ ^ 2 ≤ f x := by
  set h := x - y with hh
  let ψ : ℝ → ℝ := fun t => f (y + t • h) - t * inner ℝ (f' y) h - γ / 2 * t ^ 2 * ‖h‖ ^ 2
  let ψ' : ℝ → ℝ := fun t => inner ℝ (f' (y + t • h)) h - inner ℝ (f' y) h - γ * t * ‖h‖ ^ 2
  have hd : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => y + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add y
    have hf := ((hg (y + t • h)).hasFDerivAt).comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (f' y) h) (inner ℝ (f' y) h) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (f' y) h)
    have h3 : HasDerivAt (fun s : ℝ => γ / 2 * s ^ 2 * ‖h‖ ^ 2) (γ * t * ‖h‖ ^ 2) t := by
      have h0 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact ((h0.const_mul (γ / 2)).mul_const (‖h‖ ^ 2)).congr_deriv (by ring)
    have hf' : HasDerivAt (fun s : ℝ => f (y + s • h)) (inner ℝ (f' (y + t • h)) h) t := hf
    exact (hf'.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope ψ ψ' (zero_lt_one' ℝ)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
  have hc0 : 0 < c := hc.1
  have hpos : 0 ≤ ψ' c := by
    have := hm (y + c • h) y
    have e1 : y + c • h - y = c • h := by abel
    rw [e1, norm_smul, inner_smul_right, inner_sub_left] at this
    simp only [Real.norm_eq_abs, abs_of_pos hc0] at this
    simp only [ψ']
    have : c * (γ * c * ‖h‖ ^ 2) ≤ c * (inner ℝ (f' (y + c • h)) h - inner ℝ (f' y) h) := by
      nlinarith
    have := le_of_mul_le_mul_left this hc0
    linarith
  rw [hcd] at hpos
  simp only [ψ, sub_zero, div_one, zero_smul, add_zero, one_smul, zero_mul, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow] at hpos
  have hx : y + h = x := by rw [hh]; abel
  rw [hx] at hpos
  linarith

/-- The one-step Lyapunov inequality, in an orthogonal splitting. -/
theorem key {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (M : Submodule ℝ Y) [M.HasOrthogonalProjection] {r ρ γ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ 2 * r) (l z0 u z : Y) (hu : u ∈ Mᗮ) (ha : l + r • u - r • z0 ∈ M)
    (hb : γ * ‖z‖ ^ 2 ≤ inner ℝ (l + r • (u - z)) z) :
    ‖M.starProjection (l + ρ • (u - z))‖ ^ 2 + ρ * r * ‖z - M.starProjection z‖ ^ 2
      + 2 * ρ * γ * ‖z‖ ^ 2
      ≤ ‖M.starProjection l‖ ^ 2 + ρ * r * ‖z0 - M.starProjection z0‖ ^ 2 := by
  set q := M.starProjection l with hq_def
  set c := M.starProjection z with hc_def
  set c0 := M.starProjection z0 with hc0_def
  have hq : q ∈ M := M.starProjection_apply_mem l
  have hc : c ∈ M := M.starProjection_apply_mem z
  have hc0 : c0 ∈ M := M.starProjection_apply_mem z0
  have hpl : l - q ∈ Mᗮ := M.sub_starProjection_mem_orthogonal l
  have hav : z - c ∈ Mᗮ := M.sub_starProjection_mem_orthogonal z
  have ha0 : z0 - c0 ∈ Mᗮ := M.sub_starProjection_mem_orthogonal z0
  set pl := l - q with hpl_def
  set a := z - c with ha_def
  set a0 := z0 - c0 with ha0_def
  have hQu : M.starProjection u = 0 := (Submodule.starProjection_apply_eq_zero_iff M).2 hu
  have hQ : M.starProjection (l + ρ • (u - z)) = q - ρ • c := by
    rw [map_add, map_smul, map_sub, hQu, zero_sub, smul_neg, ← sub_eq_add_neg]
  -- the P-part of the step-1 residual vanishes
  have hw0 : pl + r • u - r • a0 = 0 := by
    have h1 : pl + r • u - r • a0 ∈ Mᗮ :=
      Mᗮ.sub_mem (Mᗮ.add_mem hpl (Mᗮ.smul_mem r hu)) (Mᗮ.smul_mem r ha0)
    have h2 : pl + r • u - r • a0 ∈ M := by
      have : pl + r • u - r • a0 = (l + r • u - r • z0) - (q - r • c0) := by
        simp only [hpl_def, ha0_def]; module
      rw [this]
      exact M.sub_mem ha (M.sub_mem hq (M.smul_mem r hc0))
    have := Submodule.inner_right_of_mem_orthogonal h2 h1
    exact inner_self_eq_zero.1 this
  have hlv : l + r • (u - z) = r • a0 + q - r • a - r • c := by
    have : l + r • (u - z) = (pl + r • u - r • a0) + r • a0 + q - r • a - r • c := by
      simp only [hpl_def, ha_def]; module
    rw [this, hw0, zero_add]
  have hz : z = a + c := by simp [ha_def]
  have o1 : inner ℝ a0 c = 0 := Submodule.inner_left_of_mem_orthogonal hc ha0
  have o2 : inner ℝ a c = 0 := Submodule.inner_left_of_mem_orthogonal hc hav
  have o3 : inner ℝ q a = 0 := Submodule.inner_right_of_mem_orthogonal hq hav
  have o4 : inner ℝ c a = 0 := Submodule.inner_right_of_mem_orthogonal hc hav
  have hn : ‖z‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    rw [hz, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, o2, o4]; ring
  have hb' : γ * ‖z‖ ^ 2 ≤ r * inner ℝ a0 a + inner ℝ q c - r * ‖a‖ ^ 2 - r * ‖c‖ ^ 2 := by
    have e : inner ℝ (l + r • (u - z)) z
        = r * inner ℝ a0 a + inner ℝ q c - r * ‖a‖ ^ 2 - r * ‖c‖ ^ 2 := by
      rw [hlv]
      conv_lhs => rw [hz]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_smul_left,
        o1, o2, o3, o4, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
      ring
    linarith
  have hqc : ‖q - ρ • c‖ ^ 2 = ‖q‖ ^ 2 - 2 * ρ * inner ℝ q c + ρ ^ 2 * ‖c‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]; ring
  have hd : 0 ≤ ‖a0‖ ^ 2 - 2 * inner ℝ a0 a + ‖a‖ ^ 2 := by
    have := norm_sub_sq_real a0 a
    nlinarith [sq_nonneg ‖a0 - a‖]
  rw [hQ, hqc]
  have hc2 : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hb' (by linarith : (0:ℝ) ≤ 2 * ρ),
    mul_nonneg hρ.le hd, mul_nonneg hρ.le (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * r - ρ) hc2)]

theorem fin_of {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : ∃ x : ℝ, e = x :=
  ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩

end GMyT5ddb

open Filter Topology InertialFB.IFB GabayMercier.DualAlgorithm in
theorem solution {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) (hρr : ρ ≤ 2 * r) :
    Tendsto y atTop (𝓝 ys) := by
  obtain ⟨hsp1, hsp2⟩ := hsp
  simp only [lagrangian] at hsp1 hsp2
  -- f₂ ys is finite
  have hys_top : f₂ ys ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := h.f₂_proper.2
    obtain ⟨X, hX⟩ := GMyT5ddb.fin_of hx (h.f₂_proper.1 x)
    have := hsp2 vs x
    rw [htop, EReal.coe_add_top, top_le_iff, hX, ← EReal.coe_add] at this
    exact EReal.coe_ne_top _ this
  obtain ⟨F, hF⟩ := GMyT5ddb.fin_of hys_top (h.f₂_proper.1 ys)
  -- ys = A vs
  have hys : A vs = ys := by
    have h1 := hsp1 (ls + (A vs - ys))
    rw [hF, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_add_left,
      real_inner_self_eq_norm_sq] at h1
    have h2 : ‖A vs - ys‖ ^ 2 ≤ 0 := by linarith
    have h3 : ‖A vs - ys‖ = 0 := by nlinarith [norm_nonneg (A vs - ys)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  subst hys
  -- ⟪ls, A w⟫ = b w
  have hlb : ∀ w, inner ℝ ls (A w) = b w := by
    have hφ : ∀ w, 0 ≤ inner ℝ ls (A w) - b w := by
      intro w
      have h1 := hsp2 (vs + w) (A vs)
      rw [hF, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      simp only [map_add, sub_self, inner_zero_right, add_sub_cancel_left] at h1
      linarith
    intro w
    have h1 := hφ w
    have h2 := hφ (-w)
    simp only [map_neg, inner_neg_right] at h2
    linarith
  -- one-step inequality: γ/2 ‖z‖² ≤ ⟪l + r(u - z), z⟫
  have hstep : ∀ n, γ / 2 * ‖y (n + 1) - A vs‖ ^ 2 ≤
      inner ℝ ((lam n - ls) + r • ((A (v (n + 1)) - A vs) - (y (n + 1) - A vs)))
        (y (n + 1) - A vs) := by
    intro n
    obtain ⟨_, hsub, _⟩ := hrun n
    set y' := y (n + 1) with hy'
    set g := lam n + r • A (v (n + 1)) - r • y' - f₁' y' with hg
    obtain ⟨hy'top, hsg⟩ := hsub
    obtain ⟨F', hF'⟩ := GMyT5ddb.fin_of hy'top (h.f₂_proper.1 y')
    have e1 := hsp2 vs y'
    rw [hF, hF', ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at e1
    simp only [sub_self, inner_zero_right, add_zero] at e1
    have e2 := hsg (A vs)
    rw [hF, hF', ← EReal.coe_add, EReal.coe_le_coe_iff] at e2
    have e3 := GMyT5ddb.strong_cvx h.f₁_hasGradient h.strongMono (A vs) y'
    have hv : (lam n - ls) + r • ((A (v (n + 1)) - A vs) - (y' - A vs)) = g + f₁' y' - ls := by
      rw [hg]; module
    have hz : y' - A vs = -(A vs - y') := by abel
    rw [hv, hz, inner_neg_right, inner_sub_left, inner_add_left, norm_neg]
    linarith
  -- projection setup
  set M : Submodule ℝ Y := (LinearMap.range (A : V →ₗ[ℝ] Y))ᗮ with hM
  set E : ℕ → ℝ := fun n => ‖M.starProjection (lam n - ls)‖ ^ 2
    + ρ * r * ‖(y n - A vs) - M.starProjection (y n - A vs)‖ ^ 2 with hE
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    simp only [hE]; positivity
  have hdec : ∀ n, E (n + 1) + ρ * γ * ‖y (n + 1) - A vs‖ ^ 2 ≤ E n := by
    intro n
    obtain ⟨h1, _, h3⟩ := hrun n
    have hu : A (v (n + 1)) - A vs ∈ Mᗮ := by
      apply Submodule.le_orthogonal_orthogonal
      exact ⟨v (n + 1) - vs, by simp⟩
    have ha : (lam n - ls) + r • (A (v (n + 1)) - A vs) - r • (y n - A vs) ∈ M := by
      rw [hM, Submodule.mem_orthogonal]
      rintro x ⟨w, rfl⟩
      have := h1 w
      rw [← hlb w] at this
      simp only [ContinuousLinearMap.coe_coe, inner_add_right, inner_sub_right,
        inner_smul_right, inner_sub_left, real_inner_smul_left] at this ⊢
      rw [real_inner_comm (A w) (lam n), real_inner_comm (A w) ls,
        real_inner_comm (A w) (A (v (n + 1))), real_inner_comm (A w) (y n)] at this
      linarith
    have hk := GMyT5ddb.key M hρ hρr (lam n - ls) (y n - A vs) (A (v (n + 1)) - A vs)
      (y (n + 1) - A vs) (γ := γ / 2) hu ha (hstep n)
    have hl : lam (n + 1) - ls
        = (lam n - ls) + ρ • ((A (v (n + 1)) - A vs) - (y (n + 1) - A vs)) := by
      rw [h3]; module
    simp only [hE]
    rw [hl]
    linarith
  -- summability
  have hργ : 0 < ρ * γ := mul_pos hρ h.γ_pos
  set f : ℕ → ℝ := fun k => ρ * γ * ‖y (k + 1) - A vs‖ ^ 2 with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have hsum : ∀ N, ∑ k ∈ Finset.range N, f k ≤ E 0 - E N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hdec N
      simp only [hf] at ih ⊢
      linarith
  have hs : Summable f :=
    summable_of_sum_range_le (c := E 0) hfnn (fun N => by linarith [hsum N, hE0 N])
  have ht := hs.tendsto_atTop_zero
  have ht2 : Tendsto (fun k => ‖y (k + 1) - A vs‖) atTop (𝓝 0) := by
    have := (ht.div_const (ρ * γ)).sqrt
    simp only [zero_div, Real.sqrt_zero] at this
    refine this.congr (fun k => ?_)
    simp only [hf]
    rw [mul_div_cancel_left₀ _ hργ.ne', Real.sqrt_sq (norm_nonneg _)]
  have ht3 : Tendsto (fun k => y (k + 1)) atTop (𝓝 (A vs)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 ht2
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 ht3
