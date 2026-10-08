-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.theorem_3_18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:50:26.55772+00:00
-- url     : https://prove2.me/submissions/84a4fd87-2574-45af-829d-23f4ae834125

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

set_option autoImplicit false

open scoped InnerProductSpace

theorem f659ce50_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (a b : EuclideanSpace ℝ (Fin n)) :
    f b ≤ f a + inner ℝ (g a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let p : ℝ → EuclideanSpace ℝ (Fin n) := fun s => a + s • v
  let G : ℝ → ℝ := fun s => f (p s) - f a - s * inner ℝ (g a) v - β / 2 * s ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ s : ℝ, HasDerivAt G
      (inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2) s := by
    intro s
    have hpd : HasDerivAt p v s := by
      have := ((hasDerivAt_id s).smul_const v).const_add a
      simpa [p] using this
    have hfg : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (g (p s))) (p s) :=
      hasGradientAt_iff_hasFDerivAt.mp (hgrad (p s))
    have h1 := hfg.comp_hasDerivAt s hpd
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g a) v) (inner ℝ (g a) v) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (g a) v)
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h1' : HasDerivAt (fun s => f (p s)) (inner ℝ (g (p s)) v) s := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
    exact ((h1'.sub_const (f a)).sub h2).sub h3
  have hnonpos : ∀ s ∈ Set.Icc (0:ℝ) 1,
      inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2 ≤ 0 := by
    intro s hs
    have hle := hlip (p s) a
    have hps : p s - a = s • v := by simp [p]
    rw [hps, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hle
    have hcs := real_inner_le_norm (g (p s) - g a) v
    rw [inner_sub_left] at hcs
    have : ‖g (p s) - g a‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    nlinarith
  have hanti : AntitoneOn G (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s _; exact (hderiv s).continuousAt.continuousWithinAt
    · intro s _
      exact (hderiv s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s).deriv]
      exact hnonpos s (interior_subset hs)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = b := by simp [p, v]
  simp only [G, hp0, hp1] at h01
  nlinarith

/-- One step of the Lyapunov decrease for Nesterov's method (strongly convex case). -/
theorem f659ce50_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α β r : ℝ) (hα : 0 < α) (hr : 1 ≤ r) (hβ : β = α * r ^ 2)
    (x y xs g y2 x2 : E) (fx fy fy2 fs : ℝ)
    (hy2 : y2 = x - (1 / β) • g)
    (hx2 : x2 = (1 + (r - 1) / (r + 1)) • y2 - ((r - 1) / (r + 1)) • y)
    (h1 : fy2 ≤ fx + ⟪g, y2 - x⟫_ℝ + β / 2 * ‖y2 - x‖ ^ 2)
    (h2 : fx + ⟪g, y - x⟫_ℝ ≤ fy)
    (h3 : fx + ⟪g, xs - x⟫_ℝ + α / 2 * ‖xs - x‖ ^ 2 ≤ fs) :
    fy2 - fs + α / 2 * ‖((1 + r) • x2 - r • y2) - xs‖ ^ 2 ≤
      (1 - 1 / r) * (fy - fs + α / 2 * ‖((1 + r) • x - r • y) - xs‖ ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hr1 : r + 1 ≠ 0 := by linarith
  have hβ0 : β ≠ 0 := by rw [hβ]; positivity
  set d := y - x with hd
  set u := xs - x with hu
  have hy : y = x + d := by rw [hd]; abel
  have hxs : xs = x + u := by rw [hu]; abel
  have e1 : y2 - x = -(1 / β) • g := by rw [hy2]; simp [neg_smul, sub_eq_add_neg]
  have e2 : ((1 + r) • x2 - r • y2) - xs = -(r / β) • g - (r - 1) • d - u := by
    rw [hx2, hy2, hy, hxs]
    match_scalars <;> field_simp <;> ring
  have e3 : ((1 + r) • x - r • y) - xs = -r • d - u := by
    rw [hy, hxs]
    match_scalars <;> ring
  rw [e1] at h1
  rw [e2, e3]
  rw [← real_inner_self_eq_norm_sq] at h1 h3
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_neg_right, real_inner_smul_left, real_inner_smul_right] at h1 ⊢
  simp only [real_inner_comm d g, real_inner_comm u g, real_inner_comm d u] at h2 h3 ⊢
  have hD : 0 ≤ ⟪d, d⟫_ℝ := real_inner_self_nonneg
  subst hβ
  generalize ⟪g, g⟫_ℝ = G at h1 ⊢
  generalize ⟪d, g⟫_ℝ = gd at h2 ⊢
  generalize ⟪u, g⟫_ℝ = gu at h3 ⊢
  generalize ⟪u, d⟫_ℝ = du at ⊢
  generalize ⟪u, u⟫_ℝ = U at h3 ⊢
  generalize ⟪d, d⟫_ℝ = D at hD ⊢
  have hq : 0 ≤ 1 - 1 / r := by
    rw [sub_nonneg, div_le_one hr0]; exact hr
  have k1 := mul_nonneg hq (sub_nonneg.2 h2)
  have k2 := mul_nonneg (le_of_lt (one_div_pos.2 hr0)) (sub_nonneg.2 h3)
  have k3 : 0 ≤ (r - 1) * α / 2 * D :=
    mul_nonneg (div_nonneg (mul_nonneg (by linarith) hα.le) (by norm_num)) hD
  have k4 := sub_nonneg.2 h1
  rw [← sub_nonneg]
  suffices h : 0 ≤ (1 - 1 / r) * (fy - (fx + gd)) + 1 / r * (fs - (fx + gu + α / 2 * U)) +
      ((fx + -(1 / (α * r ^ 2)) * G + α * r ^ 2 / 2 *
        (-(1 / (α * r ^ 2)) * (-(1 / (α * r ^ 2)) * G))) - fy2) + (r - 1) * α / 2 * D by
    convert h using 1
    field_simp
    ring
  linarith

open ConvexOptAlg.NesterovStrong in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xstar ≤
      (α + β) / 2 * ‖x 1 - xstar‖ ^ 2 * Real.exp (-(((t : ℝ) - 1) / Real.sqrt (kappa α β))) := by
  have hdesc := f659ce50_descent f g β hsm.1 hsm.2
  have hlow : ∀ a b, f a + ⟪g a, b - a⟫_ℝ + α / 2 * ‖b - a‖ ^ 2 ≤ f b :=
    fun a b => hsc a (Set.mem_univ _) b (Set.mem_univ _)
  have hexp_pos : 0 < Real.exp (-(((t : ℝ) - 1) / Real.sqrt (kappa α β))) := Real.exp_pos _
  by_cases hab : α ≤ β
  swap
  · -- degenerate: α > β forces the space to be trivial
    push Not at hab
    have heq : ∀ a b : EuclideanSpace ℝ (Fin n), b = a := by
      intro a b
      have h1 := hdesc a b
      have h2 := hlow a b
      have h3 : ‖b - a‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖b - a‖]
      have h4 : ‖b - a‖ = 0 := by nlinarith [norm_nonneg (b - a)]
      exact sub_eq_zero.mp (norm_eq_zero.mp h4)
    rw [heq xstar (y t), heq xstar (x 1)]
    simp
  -- main case
  set r := Real.sqrt (kappa α β) with hr_def
  have hk : 1 ≤ kappa α β := by
    unfold kappa; rw [le_div_iff₀ hα]; linarith
  have hr1 : 1 ≤ r := by rw [hr_def]; exact Real.one_le_sqrt.mpr hk
  have hr0 : 0 < r := by linarith
  have hrsq : r ^ 2 = β / α := by
    rw [hr_def, Real.sq_sqrt (by linarith)]; rfl
  have hβr : β = α * r ^ 2 := by rw [hrsq]; field_simp
  -- g vanishes at the minimizer
  have hg0 : g xstar = 0 := by
    have h1 := hdesc xstar (xstar - (1 / β) • g xstar)
    have h2 := hmin (xstar - (1 / β) • g xstar)
    have e : xstar - (1 / β) • g xstar - xstar = -(1 / β) • g xstar := by
      rw [neg_smul]; abel
    rw [e, inner_smul_right, norm_smul, real_inner_self_eq_norm_sq] at h1
    have hn : ‖-(1 / β)‖ = 1 / β := by
      rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    rw [hn] at h1
    have h3 : ‖g xstar‖ ^ 2 ≤ 0 := by
      have : -(1 / β) * ‖g xstar‖ ^ 2 + β / 2 * (1 / β * ‖g xstar‖) ^ 2
          = -(1 / (2 * β)) * ‖g xstar‖ ^ 2 := by field_simp; ring
      have h5 : 0 ≤ -(1 / (2 * β)) * ‖g xstar‖ ^ 2 := by linarith
      have h6 : 0 < 1 / (2 * β) := by positivity
      nlinarith
    have h4 : ‖g xstar‖ = 0 := by nlinarith [norm_nonneg (g xstar)]
    exact norm_eq_zero.mp h4
  -- Lyapunov function
  set L : ℕ → ℝ := fun s => f (y s) - f xstar + α / 2 * ‖((1 + r) • x s - r • y s) - xstar‖ ^ 2
    with hL
  have hstep : ∀ s, 1 ≤ s → L (s + 1) ≤ (1 - 1 / r) * L s := by
    intro s hs
    obtain ⟨hy, hx⟩ := hrun.2 s hs
    have h1 := hdesc (x s) (y (s + 1))
    have h2 : f (x s) + ⟪g (x s), y s - x s⟫_ℝ ≤ f (y s) := by
      have := hlow (x s) (y s); nlinarith [sq_nonneg ‖y s - x s‖]
    have h3 := hlow (x s) xstar
    exact f659ce50_step α β r hα hr1 hβr (x s) (y s) xstar (g (x s)) (y (s + 1)) (x (s + 1))
      (f (x s)) (f (y s)) (f (y (s + 1))) (f xstar) hy hx h1 h2 h3
  have hq0 : 0 ≤ 1 - 1 / r := by
    rw [sub_nonneg, div_le_one hr0]; exact hr1
  have hiter : ∀ k : ℕ, L (k + 1) ≤ (1 - 1 / r) ^ k * L 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc L (k + 1 + 1) ≤ (1 - 1 / r) * L (k + 1) := hstep (k + 1) (by omega)
        _ ≤ (1 - 1 / r) * ((1 - 1 / r) ^ k * L 1) := mul_le_mul_of_nonneg_left ih hq0
        _ = (1 - 1 / r) ^ (k + 1) * L 1 := by ring
  have hL1 : L 1 ≤ (α + β) / 2 * ‖x 1 - xstar‖ ^ 2 := by
    have hx1 : (1 + r) • x 1 - r • y 1 = x 1 := by
      rw [← hrun.1]; module
    simp only [hL, hx1]
    rw [← hrun.1]
    have h1 := hdesc xstar (x 1)
    rw [hg0, inner_zero_left] at h1
    have : ‖x 1 - xstar‖ = ‖x 1 - xstar‖ := rfl
    nlinarith
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hyL : f (y (k + 1)) - f xstar ≤ L (k + 1) := by
    simp only [hL]; nlinarith [sq_nonneg ‖(1 + r) • x (k + 1) - r • y (k + 1) - xstar‖]
  have hB : 0 ≤ (α + β) / 2 * ‖x 1 - xstar‖ ^ 2 := by positivity
  have hpow : (1 - 1 / r) ^ k ≤ Real.exp (-((((k + 1 : ℕ) : ℝ) - 1) / r)) := by
    have e : -((((k + 1 : ℕ) : ℝ) - 1) / r) = (k : ℝ) * (-(1 / r)) := by push_cast; ring
    rw [e, Real.exp_nat_mul]
    apply pow_le_pow_left₀ hq0
    have := Real.add_one_le_exp (-(1 / r))
    linarith
  calc f (y (k + 1)) - f xstar ≤ L (k + 1) := hyL
    _ ≤ (1 - 1 / r) ^ k * L 1 := hiter k
    _ ≤ (1 - 1 / r) ^ k * ((α + β) / 2 * ‖x 1 - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hL1 (pow_nonneg hq0 k)
    _ ≤ Real.exp (-((((k + 1 : ℕ) : ℝ) - 1) / r)) * ((α + β) / 2 * ‖x 1 - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hpow hB
    _ = _ := by ring
