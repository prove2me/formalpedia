-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.theorem_3_19
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:05:46.155596+00:00
-- url     : https://prove2.me/submissions/4c3b959d-2f0a-4f20-b790-1142d244dc29

/-
Bubeck, Convex Optimization: Algorithms and Complexity, Theorem 3.19: Nesterov's accelerated gradient
descent on a convex `β`-smooth function satisfies `f(y_t) - f(x*) ≤ 2β‖x_1 - x*‖²/t²`.

With `λ_0 = 0`, `λ_{s+1} = (1 + √(1 + 4λ_s²))/2` (so `λ_{s+1}² = λ_{s+1} + λ_s²` and `λ_s ≥ (s+1)/2`),
`δ_s = f(y_s) - f(x*)` and `u_s = λ_s x_s - (λ_s - 1) y_s - x*`:
* the run gives `u_{s+1} = u_s - (λ_s/β) ∇f(x_s)` (using `λ_{s+1} γ_s = 1 - λ_s`);
* the one-step inequality `f(x - ∇f(x)/β) - f(y) ≤ ⟨∇f(x), x - y⟩ - ‖∇f(x)‖²/(2β)`, taken with
  `y = y_s` (weight `λ_s - 1`) and `y = x*` (weight 1), gives
  `λ_s² δ_{s+1} - λ_{s-1}² δ_s ≤ (β/2)(‖u_s‖² - ‖u_{s+1}‖²)`;
* telescoping, `λ_{t-1}² δ_t ≤ (β/2)‖u_1‖² = (β/2)‖x_1 - x*‖²`, and `λ_{t-1} ≥ t/2`.
The one-step inequality is the quadratic upper bound of a `β`-smooth function and the first-order
inequality of a convex function, both proved here along the segment `x + s(y - x)`.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs

set_option autoImplicit false

namespace GDLib

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem line_deriv {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hg (x + t • d)).hasFDerivAt
  have := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

/-- First-order condition for a convex differentiable function. -/
theorem first_order {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hconv : ConvexOn ℝ Set.univ f) (x y : E) : f x + inner ℝ (g x) (y - x) ≤ f y := by
  have hc : ConvexOn ℝ Set.univ (fun s : ℝ => f (x + s • (y - x))) := by
    have := hconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    have e : (fun s : ℝ => f (x + s • (y - x))) = f ∘ ⇑(AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) := by
      funext s; simp [AffineMap.lineMap_apply, add_comm]
    rw [e]
    simpa using this
  have hd := line_deriv hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp [slope_def_field] at this
  linarith

/-- Quadratic upper bound for a function with `β`-Lipschitz gradient. -/
theorem quad_upper {f : E → ℝ} {g : E → E} {β : ℝ} (hg : ∀ z, HasGradientAt f (g z) z)
    (hL : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (x y : E) :
    f y ≤ f x + inner ℝ (g x) (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * inner ℝ (g x) d - β / 2 * t ^ 2 * ‖d‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - β * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hg x d t
    have h2 : HasDerivAt (fun t : ℝ => t * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun t : ℝ => β / 2 * t ^ 2 * ‖d‖ ^ 2) (β * t * ‖d‖ ^ 2) t := by
      refine (((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖d‖ ^ 2)).congr_deriv ?_
      rw [show (2 - 1 : ℕ) = 1 from rfl]
      push_cast
      ring
    exact (((h1.sub (hasDerivAt_const t (f x))).sub h2).sub h3).congr_deriv (by ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun t _ => (hψd t).continuousAt.continuousWithinAt)
      (fun t _ => (hψd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hψd t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have h1 : inner ℝ (g (x + t • d) - g x) d ≤ β * t * ‖d‖ ^ 2 := by
      calc inner ℝ (g (x + t • d) - g x) d ≤ ‖g (x + t • d) - g x‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (β * ‖x + t • d - x‖) * ‖d‖ := by gcongr; exact hL _ _
        _ = β * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]; ring
    rw [inner_sub_left] at h1
    linarith
  have := hanti (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [hψ] at this
  have hxd : x + d = y := by simp [hd]
  simp at this
  rw [hxd] at this
  linarith


open ConvexOptAlg.NesterovSmooth in
theorem lam_succ_sq (s : ℕ) : lam (s + 1) ^ 2 = lam (s + 1) + lam s ^ 2 := by
  have hD : 0 ≤ 1 + 4 * lam s ^ 2 := by positivity
  have h := Real.sq_sqrt hD
  show ((1 + Real.sqrt (1 + 4 * lam s ^ 2)) / 2) ^ 2 =
    (1 + Real.sqrt (1 + 4 * lam s ^ 2)) / 2 + lam s ^ 2
  nlinarith [h]

open ConvexOptAlg.NesterovSmooth in
theorem lam_nonneg (s : ℕ) : 0 ≤ lam s := by
  induction s with
  | zero => simp [lam]
  | succ s ih => show 0 ≤ (1 + Real.sqrt (1 + 4 * lam s ^ 2)) / 2; positivity

open ConvexOptAlg.NesterovSmooth in
theorem lam_succ_ge (s : ℕ) : lam s + 1 / 2 ≤ lam (s + 1) := by
  have hs := lam_nonneg s
  have : 2 * lam s ≤ Real.sqrt (1 + 4 * lam s ^ 2) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  show lam s + 1 / 2 ≤ (1 + Real.sqrt (1 + 4 * lam s ^ 2)) / 2
  linarith

open ConvexOptAlg.NesterovSmooth in
theorem lam_one : lam 1 = 1 := by
  show (1 + Real.sqrt (1 + 4 * lam 0 ^ 2)) / 2 = 1
  simp [lam]

open ConvexOptAlg.NesterovSmooth in
theorem lam_ge (s : ℕ) (hs : 1 ≤ s) : ((s : ℝ) + 1) / 2 ≤ lam s := by
  induction s, hs using Nat.le_induction with
  | base => rw [lam_one]; norm_num
  | succ s hs ih =>
    have := lam_succ_ge s
    push_cast
    linarith

open ConvexOptAlg.NesterovSmooth in
theorem lam_succ_pos (s : ℕ) : 1 ≤ lam (s + 1) := by
  have := lam_succ_ge s
  have := lam_nonneg s
  have h1 : 1 ≤ lam (s + 1) := by
    show 1 ≤ (1 + Real.sqrt (1 + 4 * lam s ^ 2)) / 2
    have : 1 ≤ Real.sqrt (1 + 4 * lam s ^ 2) := by
      apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg (lam s)]
    linarith
  exact h1

open ConvexOptAlg.NesterovSmooth in
theorem lam_gam (s : ℕ) : lam (s + 1) * gam s = 1 - lam s := by
  unfold gam
  have : lam (s + 1) ≠ 0 := by have := lam_succ_pos s; linarith
  field_simp

theorem grad_zero_of_min {f : E → ℝ} {g : E → E} {β : ℝ} (hg : ∀ z, HasGradientAt f (g z) z)
    (hL : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) (xs : E) (hmin : ∀ y, f xs ≤ f y) :
    g xs = 0 := by
  have hβne : β ≠ 0 := hβ.ne'
  have h1 := quad_upper hg hL hβ.le xs (xs - (1 / β) • g xs)
  have h2 := hmin (xs - (1 / β) • g xs)
  have e1 : inner ℝ (g xs) (xs - (1 / β) • g xs - xs) = - (1 / β) * ‖g xs‖ ^ 2 := by
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ‖xs - (1 / β) • g xs - xs‖ ^ 2 = (1 / β) ^ 2 * ‖g xs‖ ^ 2 := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  rw [e1, e2] at h1
  have e3 : - (1 / β) * ‖g xs‖ ^ 2 + β / 2 * ((1 / β) ^ 2 * ‖g xs‖ ^ 2) =
      - (‖g xs‖ ^ 2 * (1 / (2 * β))) := by
    field_simp; ring
  have h3 : ‖g xs‖ ^ 2 * (1 / (2 * β)) ≤ 0 := by linarith
  have hpos : 0 < 1 / (2 * β) := by positivity
  have : ‖g xs‖ ^ 2 ≤ 0 := le_of_mul_le_mul_right (by simpa using h3) hpos
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg (g xs)])

/-- One gradient step against any comparison point (Bubeck, Lemma 3.6 style). -/
theorem step_lemma {f : E → ℝ} {g : E → E} {β : ℝ} (hg : ∀ z, HasGradientAt f (g z) z)
    (hL : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) (hconv : ConvexOn ℝ Set.univ f)
    (x y : E) :
    f (x - (1 / β) • g x) - f y ≤ inner ℝ (g x) (x - y) - 1 / (2 * β) * ‖g x‖ ^ 2 := by
  have hβne : β ≠ 0 := hβ.ne'
  have q := quad_upper hg hL hβ.le x (x - (1 / β) • g x)
  have fo := first_order hg hconv x y
  have e1 : inner ℝ (g x) (x - (1 / β) • g x - x) = - (1 / β) * ‖g x‖ ^ 2 := by
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ‖x - (1 / β) • g x - x‖ ^ 2 = (1 / β) ^ 2 * ‖g x‖ ^ 2 := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  rw [e1, e2] at q
  have e3 : - (1 / β) * ‖g x‖ ^ 2 + β / 2 * ((1 / β) ^ 2 * ‖g x‖ ^ 2) =
      - (1 / (2 * β) * ‖g x‖ ^ 2) := by
    field_simp; ring
  have e4 : inner ℝ (g x) (y - x) = - inner ℝ (g x) (x - y) := by
    rw [← inner_neg_right, neg_sub]
  linarith

open ConvexOptAlg.NesterovSmooth in
theorem nest_core {f : E → ℝ} {g : E → E} {β : ℝ} (hg : ∀ z, HasGradientAt f (g z) z)
    (hL : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) (hconv : ConvexOn ℝ Set.univ f)
    (xs : E) (hmin : ∀ z, f xs ≤ f z) (x y : ℕ → E) (hx1 : x 1 = y 1)
    (hrun : ∀ t : ℕ, 1 ≤ t → y (t + 1) = x t - (1 / β) • g (x t) ∧
      x (t + 1) = (1 - gam t) • y (t + 1) + gam t • y t) (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xs ≤ 2 * β * ‖x 1 - xs‖ ^ 2 / (t : ℝ) ^ 2 := by
  have hβne : β ≠ 0 := hβ.ne'
  have hgs := grad_zero_of_min hg hL hβ xs hmin
  set δ : ℕ → ℝ := fun s => f (y s) - f xs with hδ
  set u : ℕ → E := fun s => lam s • x s - (lam s - 1) • y s - xs with hu
  -- the recursion for `u`
  have hu_succ : ∀ s, 1 ≤ s → u (s + 1) = u s - (lam s / β) • g (x s) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hrun s hs
    have hl : lam (s + 1) ≠ 0 := by have := lam_succ_pos s; linarith
    have hlg := lam_gam s
    have hgam : gam s = (1 - lam s) / lam (s + 1) := rfl
    simp only [hu]
    rw [h2, h1]
    rw [hgam]
    match_scalars <;> field_simp <;> ring
  -- the one-step inequality
  have hstep : ∀ s, 1 ≤ s →
      lam s ^ 2 * δ (s + 1) - (lam s ^ 2 - lam s) * δ s ≤ β / 2 * (‖u s‖ ^ 2 - ‖u (s + 1)‖ ^ 2) := by
    intro s hs
    obtain ⟨h1, _⟩ := hrun s hs
    have hls : 1 ≤ lam s := by
      obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
      exact lam_succ_pos r
    have A1 := step_lemma hg hL hβ hconv (x s) (y s)
    have A2 := step_lemma hg hL hβ hconv (x s) xs
    rw [← h1] at A1 A2
    have hcomb : lam s * δ (s + 1) - (lam s - 1) * δ s ≤
        inner ℝ (g (x s)) (u s) - lam s / (2 * β) * ‖g (x s)‖ ^ 2 := by
      have e : inner ℝ (g (x s)) (u s) =
          (lam s - 1) * inner ℝ (g (x s)) (x s - y s) + inner ℝ (g (x s)) (x s - xs) := by
        simp only [hu]
        have : lam s • x s - (lam s - 1) • y s - xs =
            (lam s - 1) • (x s - y s) + (x s - xs) := by module
        rw [this, inner_add_right, inner_smul_right]
      have hm : (lam s - 1) * (f (y (s + 1)) - f (y s)) ≤
          (lam s - 1) * (inner ℝ (g (x s)) (x s - y s) - 1 / (2 * β) * ‖g (x s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left A1 (by linarith)
      simp only [hδ]
      calc lam s * (f (y (s + 1)) - f xs) - (lam s - 1) * (f (y s) - f xs)
          = (lam s - 1) * (f (y (s + 1)) - f (y s)) + (f (y (s + 1)) - f xs) := by ring
        _ ≤ (lam s - 1) * (inner ℝ (g (x s)) (x s - y s) - 1 / (2 * β) * ‖g (x s)‖ ^ 2) +
            (inner ℝ (g (x s)) (x s - xs) - 1 / (2 * β) * ‖g (x s)‖ ^ 2) := add_le_add hm A2
        _ = inner ℝ (g (x s)) (u s) - lam s / (2 * β) * ‖g (x s)‖ ^ 2 := by rw [e]; ring
    have hmul := mul_le_mul_of_nonneg_left hcomb (by linarith : 0 ≤ lam s)
    have hnorm : ‖u (s + 1)‖ ^ 2 = ‖u s‖ ^ 2 - 2 * (lam s / β) * inner ℝ (g (x s)) (u s) +
        (lam s / β) ^ 2 * ‖g (x s)‖ ^ 2 := by
      rw [hu_succ s hs, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow,
        Real.norm_of_nonneg (by have := lam_nonneg s; positivity), real_inner_comm]
      ring
    have e1 : lam s ^ 2 * δ (s + 1) - (lam s ^ 2 - lam s) * δ s =
        lam s * (lam s * δ (s + 1) - (lam s - 1) * δ s) := by ring
    rw [e1]
    have e2 : β / 2 * (‖u s‖ ^ 2 - ‖u (s + 1)‖ ^ 2) =
        lam s * inner ℝ (g (x s)) (u s) - lam s ^ 2 / (2 * β) * ‖g (x s)‖ ^ 2 := by
      rw [hnorm]; field_simp; ring
    rw [e2]
    have e3 : lam s * (inner ℝ (g (x s)) (u s) - lam s / (2 * β) * ‖g (x s)‖ ^ 2) =
        lam s * inner ℝ (g (x s)) (u s) - lam s ^ 2 / (2 * β) * ‖g (x s)‖ ^ 2 := by
      field_simp
    linarith
  -- telescoping
  have htel : ∀ r : ℕ, lam r ^ 2 * δ (r + 1) ≤ β / 2 * (‖u 1‖ ^ 2 - ‖u (r + 1)‖ ^ 2) := by
    intro r
    induction r with
    | zero => simp [lam]
    | succ r ih =>
      have h := hstep (r + 1) (by omega)
      have hsq := lam_succ_sq r
      have : lam (r + 1) ^ 2 - lam (r + 1) = lam r ^ 2 := by linarith
      rw [this] at h
      linarith
  have hu1 : u 1 = x 1 - xs := by
    simp only [hu, lam_one]; simp [hx1]
  have hδ1 : δ 1 ≤ β / 2 * ‖x 1 - xs‖ ^ 2 := by
    have := quad_upper hg hL hβ.le xs (y 1)
    rw [hgs, inner_zero_left] at this
    have h' : ‖y 1 - xs‖ = ‖x 1 - xs‖ := by rw [hx1]
    simp only [hδ]
    rw [h'] at this
    linarith
  by_cases ht1 : t = 1
  · subst ht1
    simp only [Nat.cast_one, one_pow, div_one]
    have : 0 ≤ β * ‖x 1 - xs‖ ^ 2 := by positivity
    nlinarith [hδ1]
  · obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
    have hr : 1 ≤ r := by omega
    have h1 := htel r
    rw [hu1] at h1
    have hn : 0 ≤ ‖u (r + 1)‖ ^ 2 := by positivity
    have h2 : lam r ^ 2 * δ (r + 1) ≤ β / 2 * ‖x 1 - xs‖ ^ 2 := by
      nlinarith [mul_nonneg hβ.le hn]
    have hlr : ((r : ℝ) + 1) / 2 ≤ lam r := lam_ge r hr
    have hr0 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hsq : (((r : ℝ) + 1) / 2) ^ 2 ≤ lam r ^ 2 := by gcongr
    have hδn : 0 ≤ δ (r + 1) := sub_nonneg.2 (hmin _)
    have h3 : (((r : ℝ) + 1) / 2) ^ 2 * δ (r + 1) ≤ β / 2 * ‖x 1 - xs‖ ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_right hsq hδn) h2
    have e : (((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by push_cast; ring
    rw [e]
    rw [le_div_iff₀ (by positivity)]
    show δ (r + 1) * ((r : ℝ) + 1) ^ 2 ≤ 2 * β * ‖x 1 - xs‖ ^ 2
    nlinarith [h3]

end GDLib

open ConvexOptAlg.NesterovSmooth in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xstar ≤ 2 * β * ‖x 1 - xstar‖ ^ 2 / (t : ℝ) ^ 2 :=
  GDLib.nest_core hf.1 hf.2 hβ hconv xstar hmin x y hrun.1 hrun.2 t ht
