-- Prove2me | solution 1 for ConvexOptAlg.SVRG.eq_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:07:11.912072+00:00
-- url     : https://prove2.me/submissions/3d39fe8a-0936-4795-b263-5595d17f1077

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

set_option autoImplicit false

open scoped InnerProductSpace

theorem svr_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} {g : H → H} (hg : ∀ x, HasGradientAt f (g x) x) (x d : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hg (x + t • d))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem svr_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} {g : H → H} {L : ℝ} (hg : ∀ x, HasGradientAt f (g x) x)
    (hL : ∀ x y : H, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : H) :
    f y ≤ f x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hf : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (inner ℝ (g (x + t • (y - x))) (y - x)) t :=
    fun t => svr_line hg x (y - x) t
  have hB : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => f x + t * inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
      (inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)) t := by
    intro t
    have h1 := ((hasDerivAt_id' t).mul_const (inner ℝ (g x) (y - x))).const_add (f x)
    have h2 := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖y - x‖ ^ 2)
    have h3 : HasDerivAt
        (fun s : ℝ => f x + s * inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * s ^ 2)
        (1 * inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (↑2 * t ^ (2 - 1))) t :=
      h1.add h2
    exact h3.congr_deriv (by norm_num)
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun t : ℝ => f (x + t • (y - x)))
    (f' := fun t => inner ℝ (g (x + t • (y - x))) (y - x))
    (B := fun t : ℝ => f x + t * inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
    (B' := fun t => inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t))
    (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).hasDerivWithinAt)
    (by simp)
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      show inner ℝ (g (x + t • (y - x))) (y - x) ≤
        inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)
      have e1 : inner ℝ (g (x + t • (y - x))) (y - x) - inner ℝ (g x) (y - x)
          = inner ℝ (g (x + t • (y - x)) - g x) (y - x) := by
        rw [inner_sub_left]
      have e2 := real_inner_le_norm (g (x + t • (y - x)) - g x) (y - x)
      have e3 := hL (x + t • (y - x)) x
      have e4 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg (y - x))
      nlinarith)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have e6 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e6, one_mul, one_pow, mul_one] at key
  linarith

theorem svr_convex_fo {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} {g : H → H} (hg : ∀ x, HasGradientAt f (g x) x)
    (hc : ConvexOn ℝ Set.univ f) (a b : H) :
    f a + inner ℝ (g a) (b - a) ≤ f b := by
  set w := b - a
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + s • w)) (inner ℝ (g (a + t • w)) w) t :=
    fun t => svr_line hg a w t
  have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => f (a + t • w)) := by
    have h0 := hc.comp_affineMap (AffineMap.lineMap a b)
    have e : (fun t : ℝ => f (a + t • w)) = f ∘ AffineMap.lineMap a b := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]
    refine h0.subset ?_ (convex_Icc 0 1)
    intro t _
    simp
  have h := hφ.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one (by simpa using hline 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : a + w = b := by simp [w]
  rw [hw] at h
  linarith

/-- Co-coercivity: `‖g z - g x‖² ≤ 2β (f z - f x - ⟪g x, z - x⟫)`. -/
theorem svr_cocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {f : H → ℝ} {g : H → H} {β : ℝ} (hβ : 0 < β) (hg : ∀ x, HasGradientAt f (g x) x)
    (hc : ConvexOn ℝ Set.univ f) (hL : ∀ x y : H, ‖g x - g y‖ ≤ β * ‖x - y‖) (z x : H) :
    ‖g z - g x‖ ^ 2 ≤ 2 * β * (f z - f x - inner ℝ (g x) (z - x)) := by
  set d := g z - g x with hd
  set b := β⁻¹ with hb
  have hβb : β * b = 1 := by rw [hb]; field_simp
  set w := z - b • d with hw
  have h1 := svr_convex_fo hg hc x w
  have h2 := svr_descent hg hL z w
  have e1 : w - x = (z - x) - b • d := by rw [hw]; abel
  have e2 : w - z = -(b • d) := by rw [hw]; abel
  rw [e1, inner_sub_right, real_inner_smul_right] at h1
  rw [e2, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h2
  have e3 : inner ℝ (g z) d - inner ℝ (g x) d = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← hd, real_inner_self_eq_norm_sq]
  have h3 : b / 2 * ‖d‖ ^ 2 ≤ f z - f x - inner ℝ (g x) (z - x) := by
    have : f z - f x - inner ℝ (g x) (z - x) ≥
        b * (inner ℝ (g z) d - inner ℝ (g x) d) - β / 2 * (b ^ 2 * ‖d‖ ^ 2) := by linarith
    rw [e3] at this
    have e4 : b * ‖d‖ ^ 2 - β / 2 * (b ^ 2 * ‖d‖ ^ 2) = b / 2 * ‖d‖ ^ 2 := by
      have : β / 2 * (b ^ 2 * ‖d‖ ^ 2) = (β * b) * (b / 2 * ‖d‖ ^ 2) := by ring
      rw [this, hβb]; ring
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 2 * β)
  have e5 : 2 * β * (b / 2 * ‖d‖ ^ 2) = (β * b) * ‖d‖ ^ 2 := by ring
  rw [e5, hβb, one_mul] at h4
  exact h4

open ConvexOptAlg.SVRG in
theorem svr_sum_grad_zero {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n)) (hm : 0 < m)
    (hg : ∀ i x, HasGradientAt (fs i) (gs i x) x)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    ∑ i, gs i xstar = 0 := by
  have hF : HasFDerivAt (fun z => ∑ i, fs i z)
      (∑ i, InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gs i xstar)) xstar :=
    HasFDerivAt.fun_sum (fun i _ => (hasGradientAt_iff_hasFDerivAt.mp (hg i xstar)))
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hloc : IsLocalMin (fun z => ∑ i, fs i z) xstar := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have h := hmin z
    simp only [objective, uniformMean, Fintype.card_fin] at h
    have := (div_le_div_iff_of_pos_right hmpos).mp h
    exact this
  have h0 := hloc.hasFDerivAt_eq_zero hF
  rw [← map_sum] at h0
  have : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (∑ i, gs i xstar) =
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) 0 := by rw [h0, map_zero]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective this

theorem svr_two_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u c : H) :
    ‖u - c‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
  have h1 := norm_sub_sq_real u c
  have h2 := norm_add_sq_real u c
  have h3 : 0 ≤ ‖u + c‖ ^ 2 := by positivity
  linarith

theorem svr_variance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}
    (hm : 0 < m) (a : Fin m → H) (G : H) (hG : ∑ i, a i = (m:ℝ) • G) :
    ∑ i, ‖a i - G‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  have e : ∀ i, ‖a i - G‖ ^ 2 = ‖a i‖ ^ 2 - 2 * inner ℝ (a i) G + ‖G‖ ^ 2 :=
    fun i => norm_sub_sq_real (a i) G
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hG,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (0:ℝ) ≤ (m:ℝ) * ‖G‖ ^ 2 := by positivity
  linarith

open scoped InnerProductSpace in open ConvexOptAlg.SVRG in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖direction gs x y i‖ ^ 2) ≤
      4 * β * (objective fs x - objective fs xstar +
        objective fs y - objective fs xstar) := by
  obtain ⟨hg, hc, hL⟩ := hfamily
  have hS := svr_sum_grad_zero fs gs xstar hm hg hmin
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  -- summed co-coercivity at a point z against xstar
  have hco : ∀ z, ∑ i, ‖gs i z - gs i xstar‖ ^ 2 ≤
      2 * β * (∑ i, fs i z - ∑ i, fs i xstar) := by
    intro z
    have h1 : ∀ i, ‖gs i z - gs i xstar‖ ^ 2 ≤
        2 * β * (fs i z - fs i xstar - inner ℝ (gs i xstar) (z - xstar)) :=
      fun i => svr_cocoercive hβ (hg i) (hc i) (hL i) z xstar
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner, hS,
      inner_zero_left, sub_zero] at h2
    exact h2
  set G := fullGradient gs y with hGdef
  have hG : ∑ i, (gs i y - gs i xstar) = (m:ℝ) • G := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, hGdef, fullGradient, smul_smul,
      mul_inv_cancel₀ hmpos.ne', one_smul]
  have hdir : ∀ i, direction gs x y i = (gs i x - gs i xstar) - ((gs i y - gs i xstar) - G) := by
    intro i; simp only [direction, hGdef]; abel
  have hpt : ∀ i, ‖direction gs x y i‖ ^ 2 ≤
      2 * ‖gs i x - gs i xstar‖ ^ 2 + 2 * ‖(gs i y - gs i xstar) - G‖ ^ 2 := by
    intro i; rw [hdir i]; exact svr_two_sq _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hvar := svr_variance hm (fun i => gs i y - gs i xstar) G hG
  have hx := hco x
  have hy := hco y
  have key : ∑ i, ‖direction gs x y i‖ ^ 2 ≤
      4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar)) := by
    nlinarith
  simp only [uniformMean, objective, Fintype.card_fin]
  have e : 4 * β * ((∑ i, fs i x) / (m:ℝ) - (∑ i, fs i xstar) / m + (∑ i, fs i y) / m -
      (∑ i, fs i xstar) / m) =
      (4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar))) / m := by
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right key hmpos.le
