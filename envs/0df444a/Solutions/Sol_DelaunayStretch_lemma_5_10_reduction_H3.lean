-- Prove2me | solution 1 for DelaunayStretch.lemma_5_10_reduction_H3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:31:03.298258+00:00
-- url     : https://prove2.me/submissions/496d9954-00cd-461b-80de-34e52955e873
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DelaunayStretch_bspline_basic_properties
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch

namespace L510

theorem basisExt_eq (p : ℕ) : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ → bsplineBasisExt p j τ = bsplineBasis p j τ := by
  induction p with
  | zero => intro j τ hτ; simp [bsplineBasisExt, bsplineBasis, bsplineDeg0Ext, not_lt.mpr hτ]
  | succ p ih => intro j τ hτ; simp only [bsplineBasisExt, bsplineBasis, ih j τ hτ, ih (j+1) τ hτ]

theorem bsplineExt_eq (l : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : bsplineExt l τ = bspline l τ :=
  basisExt_eq 3 l τ hτ

theorem tau_nonneg (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ 2 * γ / Real.pi := by
  have := Real.pi_pos; positivity

theorem VExt_eq (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ a b : ℝ) (hγ : 0 ≤ γ) :
    familyVExt V γ a b = familyV V γ a b := by
  simp only [familyVExt, familyV, bsplineExt_eq _ _ (tau_nonneg γ hγ)]

theorem RExt_eq (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ a b : ℝ) (hγ : 0 ≤ γ) :
    familyRExt R γ a b = familyR R γ a b := by
  simp only [familyRExt, familyR, bsplineExt_eq _ _ (tau_nonneg γ hγ)]

theorem V_diff_a (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ b : ℝ) :
    Differentiable ℝ (fun a => familyV V γ a b) := by
  unfold familyV DelaunayStretch.bernstein
  fun_prop

theorem V_diff_b (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ a : ℝ) :
    Differentiable ℝ (fun b => familyV V γ a b) := by
  unfold familyV DelaunayStretch.bernstein
  fun_prop

theorem R_diff_a (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ b : ℝ) :
    Differentiable ℝ (fun a => familyR R γ a b) := by
  unfold familyR DelaunayStretch.bernstein
  fun_prop

theorem R_diff_b (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ a : ℝ) :
    Differentiable ℝ (fun b => familyR R γ a b) := by
  unfold familyR DelaunayStretch.bernstein
  fun_prop

theorem omega_facts (γ φ θ : ℝ) (h : (γ, φ, θ) ∈ OmegaSet) :
    |γ| < Real.pi / 2 ∧ 0 ≤ (θ - φ + γ) / (Real.pi + 2 * γ) ∧ (θ - φ + γ) / (Real.pi + 2 * γ) ≤ 1 ∧
      0 ≤ (θ + φ - γ) / (Real.pi - 2 * γ) ∧ (θ + φ - γ) / (Real.pi - 2 * γ) ≤ 1 := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hb1 := le_abs_self (γ - φ); have hb2 := neg_abs_le (γ - φ)
  have hc1 := le_abs_self (γ + φ); have hc2 := neg_abs_le (γ + φ)
  have hg : |γ| < Real.pi / 2 := by
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨g1, g2⟩ := abs_lt.mp hg
  have p1 : 0 < Real.pi + 2 * γ := by linarith
  have p2 : 0 < Real.pi - 2 * γ := by linarith
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · apply div_nonneg _ p1.le; linarith
  · rw [div_le_one p1]; linarith
  · apply div_nonneg _ p2.le; linarith
  · rw [div_le_one p2]; linarith

theorem chi_bound (x : ℝ) (hx : |x| ≤ 1) : |x - x ^ 3| ≤ 2 / 5 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  rw [abs_le]; constructor
  · nlinarith [sq_nonneg (x + 4 / 7), sq_nonneg (x - 1), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) (sq_nonneg (x + 4/7)), mul_nonneg (by linarith : (0:ℝ) ≤ x + 1) (sq_nonneg (x + 4/7))]
  · nlinarith [sq_nonneg (x - 4 / 7), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) (sq_nonneg (x - 4/7)), mul_nonneg (by linarith : (0:ℝ) ≤ x + 1) (sq_nonneg (x - 4/7))]

theorem mix_nonneg (Dv Dr χ : ℝ) (hχ : |χ| ≤ 2 / 5) (hp : 0 ≤ Dv + 2 / 5 * Dr)
    (hm : 0 ≤ Dv + -(2 / 5) * Dr) : 0 ≤ Dv + χ * Dr := by
  obtain ⟨c1, c2⟩ := abs_le.mp hχ
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 / 5 + χ) hp,
    mul_nonneg (by linarith : (0:ℝ) ≤ 2 / 5 - χ) hm]

/-- Derivative of `Ĥ` when only `a` moves. -/
theorem hhat_deriv_a (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ a b ξ c : ℝ) (hγ : 0 ≤ γ) :
    HasDerivAt (fun t => familyHhat V R Bc Dc γ (a + c * t) b ξ)
      (Real.cos γ ^ 2 * c * (deriv (fun a' => familyV V γ a' b) a +
        (ξ - ξ ^ 3) * deriv (fun a' => familyR R γ a' b) a)) 0 := by
  have e : (fun t => familyHhat V R Bc Dc γ (a + c * t) b ξ) = fun t =>
      Real.cos γ ^ 2 * familyV V γ (a + c * t) b + (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ +
        Real.cos γ ^ 2 * ((familySplineExt Bc γ + familyR R γ (a + c * t) b) * (ξ - ξ ^ 3) +
          familySplineExt Dc γ * (ξ ^ 3 - ξ ^ 5)) := by
    funext t; simp only [familyHhat, VExt_eq _ _ _ _ hγ, RExt_eq _ _ _ _ hγ]
  rw [e]
  have hl : HasDerivAt (fun t : ℝ => a + c * t) c 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add a
  have hV : HasDerivAt (fun t => familyV V γ (a + c * t) b)
      (deriv (fun a' => familyV V γ a' b) a * c) 0 := by
    have h2 : HasDerivAt (fun a' => familyV V γ a' b) (deriv (fun a' => familyV V γ a' b) a) (a + c * 0) := by
      rw [mul_zero, add_zero]; exact ((V_diff_a V γ b) a).hasDerivAt
    exact h2.comp (0:ℝ) hl
  have hR : HasDerivAt (fun t => familyR R γ (a + c * t) b)
      (deriv (fun a' => familyR R γ a' b) a * c) 0 := by
    have h2 : HasDerivAt (fun a' => familyR R γ a' b) (deriv (fun a' => familyR R γ a' b) a) (a + c * 0) := by
      rw [mul_zero, add_zero]; exact ((R_diff_a R γ b) a).hasDerivAt
    exact h2.comp (0:ℝ) hl
  have := (((hV.const_mul (Real.cos γ ^ 2)).add_const ((γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ)).add
    ((((hR.const_add (familySplineExt Bc γ)).mul_const (ξ - ξ ^ 3)).add_const
      (familySplineExt Dc γ * (ξ ^ 3 - ξ ^ 5))).const_mul (Real.cos γ ^ 2)))
  refine this.congr_deriv ?_
  ring

/-- Derivative of `Ĥ` when only `b` moves. -/
theorem hhat_deriv_b (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ a b ξ c : ℝ) (hγ : 0 ≤ γ) :
    HasDerivAt (fun t => familyHhat V R Bc Dc γ a (b + c * t) ξ)
      (Real.cos γ ^ 2 * c * (deriv (fun b' => familyV V γ a b') b +
        (ξ - ξ ^ 3) * deriv (fun b' => familyR R γ a b') b)) 0 := by
  have e : (fun t => familyHhat V R Bc Dc γ a (b + c * t) ξ) = fun t =>
      Real.cos γ ^ 2 * familyV V γ a (b + c * t) + (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ +
        Real.cos γ ^ 2 * ((familySplineExt Bc γ + familyR R γ a (b + c * t)) * (ξ - ξ ^ 3) +
          familySplineExt Dc γ * (ξ ^ 3 - ξ ^ 5)) := by
    funext t; simp only [familyHhat, VExt_eq _ _ _ _ hγ, RExt_eq _ _ _ _ hγ]
  rw [e]
  have hl : HasDerivAt (fun t : ℝ => b + c * t) c 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add b
  have hV : HasDerivAt (fun t => familyV V γ a (b + c * t))
      (deriv (fun b' => familyV V γ a b') b * c) 0 := by
    have h2 : HasDerivAt (fun b' => familyV V γ a b') (deriv (fun b' => familyV V γ a b') b) (b + c * 0) := by
      rw [mul_zero, add_zero]; exact ((V_diff_b V γ a) b).hasDerivAt
    exact h2.comp (0:ℝ) hl
  have hR : HasDerivAt (fun t => familyR R γ a (b + c * t))
      (deriv (fun b' => familyR R γ a b') b * c) 0 := by
    have h2 : HasDerivAt (fun b' => familyR R γ a b') (deriv (fun b' => familyR R γ a b') b) (b + c * 0) := by
      rw [mul_zero, add_zero]; exact ((R_diff_b R γ a) b).hasDerivAt
    exact h2.comp (0:ℝ) hl
  have := (((hV.const_mul (Real.cos γ ^ 2)).add_const ((γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ)).add
    ((((hR.const_add (familySplineExt Bc γ)).mul_const (ξ - ξ ^ 3)).add_const
      (familySplineExt Dc γ * (ξ ^ 3 - ξ ^ 5))).const_mul (Real.cos γ ^ 2)))
  refine this.congr_deriv ?_
  ring

end L510


open L510

theorem deriv_comb_a (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (γ a b s : ℝ) :
    deriv (fun a' => familyV V γ a' b + s * familyR R γ a' b) a =
      deriv (fun a' => familyV V γ a' b) a + s * deriv (fun a' => familyR R γ a' b) a := by
  rw [deriv_fun_add ((V_diff_a V γ b) a) (((R_diff_a R γ b) a).const_mul s),
    deriv_const_mul _ ((R_diff_a R γ b) a)]

theorem deriv_comb_b (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (γ a b s : ℝ) :
    deriv (fun b' => familyV V γ a b' + s * familyR R γ a b') b =
      deriv (fun b' => familyV V γ a b') b + s * deriv (fun b' => familyR R γ a b') b := by
  rw [deriv_fun_add ((V_diff_b V γ a) b) (((R_diff_b R γ a) b).const_mul s),
    deriv_const_mul _ ((R_diff_b R γ a) b)]

theorem grad_ineq_of_dirs (F : R4 → ℝ) (z : R4) (Dm Dp : ℝ)
    (hm : HasDerivAt (fun t => F (z.1, z.2.1 - t, z.2.2.1 + t, z.2.2.2)) Dm 0) (hDm : 0 ≤ Dm)
    (hp : HasDerivAt (fun t => F (z.1, z.2.1 + t, z.2.2.1 + t, z.2.2.2)) Dp 0) (hDp : 0 ≤ Dp) :
    |(gradient4 F z).2.1| ≤ (gradient4 F z).2.2.1 := by
  by_cases hd : DifferentiableAt ℝ F z
  · have hLm : HasDerivAt (fun t : ℝ => ((z.1, z.2.1 - t, z.2.2.1 + t, z.2.2.2) : R4))
        ((0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ)) 0 := by
      refine (hasDerivAt_const _ _).prodMk ?_
      refine (by simpa using (hasDerivAt_id (0:ℝ)).const_sub z.2.1 :
        HasDerivAt (fun t : ℝ => z.2.1 - t) (-1) 0).prodMk ?_
      exact (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.2.1 :
        HasDerivAt (fun t : ℝ => z.2.2.1 + t) 1 0).prodMk (hasDerivAt_const _ _)
    have hLp : HasDerivAt (fun t : ℝ => ((z.1, z.2.1 + t, z.2.2.1 + t, z.2.2.2) : R4))
        ((0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ)) 0 := by
      refine (hasDerivAt_const _ _).prodMk ?_
      refine (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.1 :
        HasDerivAt (fun t : ℝ => z.2.1 + t) 1 0).prodMk ?_
      exact (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.2.1 :
        HasDerivAt (fun t : ℝ => z.2.2.1 + t) 1 0).prodMk (hasDerivAt_const _ _)
    have cm := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hLm (by simp)
    have cp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hLp (by simp)
    have em := cm.unique hm
    have ep := cp.unique hp
    have vm : ((0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ)) =
        ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
      simp
    have vp : ((0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ)) =
        ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
      simp
    rw [vm, map_sub] at em
    rw [vp, map_add] at ep
    simp only [gradient4]
    rw [abs_le]; constructor <;> linarith
  · simp [gradient4, fderiv_zero_of_not_differentiableAt hd]


theorem pieceHc_diff (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (z : R4) (hz : |z.1| < Real.pi / 2) :
    DifferentiableAt ℝ (pieceHc V R Bc Dc) z := by
  have hpi := Real.pi_pos
  have hτ : 2 * z.1 / Real.pi < 1 := by
    rw [div_lt_one hpi]; linarith [(abs_lt.mp hz).2]
  have hb : ∀ l : ℕ, DifferentiableAt ℝ (bsplineExt l) (2 * z.1 / Real.pi) := fun l =>
    ((bspline_basic_properties.2.2.2 l).differentiableOn (by norm_num)).differentiableAt
      (Iio_mem_nhds hτ)
  have hbz : ∀ l : ℕ, DifferentiableAt ℝ (fun w : R4 => bsplineExt l (2 * w.1 / Real.pi)) z :=
    fun l => (hb l).comp z (by fun_prop)
  have h1 : Real.pi + 2 * z.1 ≠ 0 := by linarith [(abs_lt.mp hz).1]
  have h2 : Real.pi - 2 * z.1 ≠ 0 := by linarith [(abs_lt.mp hz).2]
  have h3 : Real.pi / 2 - Real.cos z.1 ≠ 0 := by
    have := Real.cos_le_one z.1; have := Real.pi_gt_three; linarith
  unfold pieceHc familyHhat familyVExt familyRExt familySplineExt posA posB balanceXi
    DelaunayStretch.bernstein
  fun_prop (disch := assumption)

theorem omega_of_ab (γ a b ψ : ℝ) (hγ : |γ| < Real.pi / 2) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    let z : R4 := (γ, γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b,
      (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b, ψ)
    z ∈ OmegaTimesR ∧ posA z = a ∧ posB z = b := by
  intro z
  obtain ⟨g1, g2⟩ := abs_lt.mp hγ
  have p1 : 0 < Real.pi / 2 + γ := by linarith
  have p2 : 0 < Real.pi / 2 - γ := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show |γ - (γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b)| <
      (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b
    rw [abs_lt]; constructor <;> nlinarith [mul_pos p1 ha0, mul_pos p2 hb0]
  · show (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b <
      Real.pi - |γ + (γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b)|
    have := mul_pos p1 (by linarith : (0:ℝ) < 1 - a)
    have := mul_pos p2 (by linarith : (0:ℝ) < 1 - b)
    rcases le_total 0 (γ + (γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b)) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; nlinarith
  · show (((Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b) -
      (γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b) + γ) / (Real.pi + 2 * γ) = a
    rw [div_eq_iff (by linarith)]; ring
  · show (((Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b) +
      (γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b) - γ) / (Real.pi - 2 * γ) = b
    rw [div_eq_iff (by linarith)]; ring

/-- The `a`- and `b`-derivatives of `Ĥ(γ, ·, ·, ψ/k)` are nonnegative in the open square, from
(H2) on the central piece. -/
theorem deriv_nonneg_of_h2 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (h2 : ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1)
    (γ ψ a b : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < Real.pi / 2)
    (hξ : |ψ / (Real.pi / 2 - Real.cos γ)| ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    let ξ := ψ / (Real.pi / 2 - Real.cos γ)
    0 ≤ deriv (fun a' => familyV V γ a' b) a + (ξ - ξ ^ 3) * deriv (fun a' => familyR R γ a' b) a ∧
    0 ≤ deriv (fun b' => familyV V γ a b') b + (ξ - ξ ^ 3) * deriv (fun b' => familyR R γ a b') b := by
  intro ξ
  have hγa : |γ| < Real.pi / 2 := by rw [abs_lt]; constructor <;> linarith [Real.pi_pos]
  obtain ⟨hzΩ, hA, hB⟩ := omega_of_ab γ a b ψ hγa ha0 ha1 hb0 hb1
  set z : R4 := (γ, γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b,
      (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b, ψ) with hz
  have hd := pieceHc_diff V R Bc Dc z hγa
  have hg := h2 z _ ⟨hzΩ, hγ0, Or.inl ⟨hξ, rfl⟩⟩
  have hcos : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hγ⟩
  have hc2 : 0 < Real.cos γ ^ 2 := by positivity
  have p1 : 0 < Real.pi + 2 * γ := by linarith [Real.pi_pos]
  have p2 : 0 < Real.pi - 2 * γ := by linarith
  -- directional derivatives
  have em : (fun t => pieceHc V R Bc Dc (z.1, z.2.1 - t, z.2.2.1 + t, z.2.2.2)) =
      fun t => familyHhat V R Bc Dc γ (a + 2 / (Real.pi + 2 * γ) * t) b ξ := by
    funext t
    simp only [pieceHc, balanceXi]
    rw [← hA, ← hB]; simp only [posA, posB, hz]; congr 2
    · field_simp; ring
    · ring_nf
  have ep : (fun t => pieceHc V R Bc Dc (z.1, z.2.1 + t, z.2.2.1 + t, z.2.2.2)) =
      fun t => familyHhat V R Bc Dc γ a (b + 2 / (Real.pi - 2 * γ) * t) ξ := by
    funext t
    simp only [pieceHc, balanceXi]
    rw [← hA, ← hB]; simp only [posA, posB, hz]; congr 2
    · ring_nf
    · field_simp; ring
  have Dm := hhat_deriv_a V R Bc Dc γ a b ξ (2 / (Real.pi + 2 * γ)) hγ0
  have Dp := hhat_deriv_b V R Bc Dc γ a b ξ (2 / (Real.pi - 2 * γ)) hγ0
  rw [← em] at Dm
  rw [← ep] at Dp
  -- identify with the gradient
  have hLm : HasDerivAt (fun t : ℝ => ((z.1, z.2.1 - t, z.2.2.1 + t, z.2.2.2) : R4))
      ((0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ)) 0 := by
    refine (hasDerivAt_const _ _).prodMk ?_
    refine (by simpa using (hasDerivAt_id (0:ℝ)).const_sub z.2.1 :
      HasDerivAt (fun t : ℝ => z.2.1 - t) (-1) 0).prodMk ?_
    exact (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.2.1 :
      HasDerivAt (fun t : ℝ => z.2.2.1 + t) 1 0).prodMk (hasDerivAt_const _ _)
  have hLp : HasDerivAt (fun t : ℝ => ((z.1, z.2.1 + t, z.2.2.1 + t, z.2.2.2) : R4))
      ((0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ)) 0 := by
    refine (hasDerivAt_const _ _).prodMk ?_
    refine (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.1 :
      HasDerivAt (fun t : ℝ => z.2.1 + t) 1 0).prodMk ?_
    exact (by simpa using (hasDerivAt_id (0:ℝ)).const_add z.2.2.1 :
      HasDerivAt (fun t : ℝ => z.2.2.1 + t) 1 0).prodMk (hasDerivAt_const _ _)
  have cm := (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hLm (by simp)).unique Dm
  have cp := (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hLp (by simp)).unique Dp
  have vm : ((0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ)) =
      ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) := by simp
  have vp : ((0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ)) =
      ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) := by simp
  rw [vm, map_sub] at cm
  rw [vp, map_add] at cp
  simp only [gradient4] at hg
  obtain ⟨g1, g2⟩ := abs_le.mp hg
  constructor
  · have : 0 ≤ Real.cos γ ^ 2 * (2 / (Real.pi + 2 * γ)) *
        (deriv (fun a' => familyV V γ a' b) a + (ξ - ξ ^ 3) * deriv (fun a' => familyR R γ a' b) a) := by
      rw [← cm]; linarith
    exact nonneg_of_mul_nonneg_right (by rwa [mul_comm] at this) (by positivity)
  · have : 0 ≤ Real.cos γ ^ 2 * (2 / (Real.pi - 2 * γ)) *
        (deriv (fun b' => familyV V γ a b') b + (ξ - ξ ^ 3) * deriv (fun b' => familyR R γ a b') b) := by
      rw [← cp]; linarith
    exact nonneg_of_mul_nonneg_right (by rwa [mul_comm] at this) (by positivity)

/-- The polynomial `p(a, b) = Ĥ(γ, a, b, ξ)` built from `V, R` (for `γ ≥ 0`). -/
noncomputable def pfun (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ ξ a b : ℝ) : ℝ :=
  Real.cos γ ^ 2 * familyV V γ a b + (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ +
    Real.cos γ ^ 2 * ((familySpline Bc γ + familyR R γ a b) * (ξ - ξ ^ 3) +
      familySpline Dc γ * (ξ ^ 3 - ξ ^ 5))

theorem pfun_hasDerivAt_a (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ ξ a b : ℝ) :
    HasDerivAt (fun a' => pfun V R Bc Dc γ ξ a' b)
      (Real.cos γ ^ 2 * (deriv (fun a' => familyV V γ a' b) a +
        (ξ - ξ ^ 3) * deriv (fun a' => familyR R γ a' b) a)) a := by
  have hV := ((V_diff_a V γ b) a).hasDerivAt
  have hR := ((R_diff_a R γ b) a).hasDerivAt
  have := (((hV.const_mul (Real.cos γ ^ 2)).add_const ((γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ)).add
    ((((hR.const_add (familySpline Bc γ)).mul_const (ξ - ξ ^ 3)).add_const
      (familySpline Dc γ * (ξ ^ 3 - ξ ^ 5))).const_mul (Real.cos γ ^ 2)))
  exact this.congr_deriv (by ring)

theorem pfun_hasDerivAt_b (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ ξ a b : ℝ) :
    HasDerivAt (fun b' => pfun V R Bc Dc γ ξ a b')
      (Real.cos γ ^ 2 * (deriv (fun b' => familyV V γ a b') b +
        (ξ - ξ ^ 3) * deriv (fun b' => familyR R γ a b') b)) b := by
  have hV := ((V_diff_b V γ a) b).hasDerivAt
  have hR := ((R_diff_b R γ a) b).hasDerivAt
  have := (((hV.const_mul (Real.cos γ ^ 2)).add_const ((γ - Real.cos γ ^ 2 * familyV V γ 0 1) * ξ)).add
    ((((hR.const_add (familySpline Bc γ)).mul_const (ξ - ξ ^ 3)).add_const
      (familySpline Dc γ * (ξ ^ 3 - ξ ^ 5))).const_mul (Real.cos γ ^ 2)))
  exact this.congr_deriv (by ring)

theorem pfun_corner_le (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (h2 : ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1)
    (γ ψ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < Real.pi / 2)
    (hξ : |ψ / (Real.pi / 2 - Real.cos γ)| ≤ 1) (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    pfun V R Bc Dc γ (ψ / (Real.pi / 2 - Real.cos γ)) 0 0 ≤
      pfun V R Bc Dc γ (ψ / (Real.pi / 2 - Real.cos γ)) a b := by
  set ξ := ψ / (Real.pi / 2 - Real.cos γ)
  have hc2 : 0 ≤ Real.cos γ ^ 2 := sq_nonneg _
  have monoA : ∀ b', 0 < b' → b' < 1 →
      MonotoneOn (fun a' => pfun V R Bc Dc γ ξ a' b') (Set.Icc 0 1) := by
    intro b' hb0' hb1'
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (fun x _ => (pfun_hasDerivAt_a V R Bc Dc γ ξ x b').continuousAt.continuousWithinAt)
    · exact (fun x _ => (pfun_hasDerivAt_a V R Bc Dc γ ξ x b').differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [interior_Icc] at hx
      rw [(pfun_hasDerivAt_a V R Bc Dc γ ξ x b').deriv]
      exact mul_nonneg hc2 (deriv_nonneg_of_h2 V R Bc Dc h2 γ ψ x b' hγ0 hγ hξ hx.1 hx.2 hb0' hb1').1
  have monoB : ∀ a', 0 < a' → a' < 1 →
      MonotoneOn (fun b' => pfun V R Bc Dc γ ξ a' b') (Set.Icc 0 1) := by
    intro a' ha0' ha1'
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (fun x _ => (pfun_hasDerivAt_b V R Bc Dc γ ξ a' x).continuousAt.continuousWithinAt)
    · exact (fun x _ => (pfun_hasDerivAt_b V R Bc Dc γ ξ a' x).differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [interior_Icc] at hx
      rw [(pfun_hasDerivAt_b V R Bc Dc γ ξ a' x).deriv]
      exact mul_nonneg hc2 (deriv_nonneg_of_h2 V R Bc Dc h2 γ ψ a' x hγ0 hγ hξ ha0' ha1' hx.1 hx.2).2
  have hcont : Continuous (fun a' => pfun V R Bc Dc γ ξ a' 0) := by
    unfold pfun familyV familyR DelaunayStretch.bernstein; fun_prop
  have hlim : Filter.Tendsto (fun a' => pfun V R Bc Dc γ ξ a' 0) (nhdsWithin 0 (Set.Ioo 0 a))
      (nhds (pfun V R Bc Dc γ ξ 0 0)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (0:ℝ) (Set.Ioo 0 a)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (ne_of_lt ha0)]; exact ⟨le_refl _, ha0.le⟩
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have h1 : pfun V R Bc Dc γ ξ ε 0 ≤ pfun V R Bc Dc γ ξ ε b :=
    monoB ε hε.1 (by linarith [hε.2]) ⟨le_refl 0, by linarith [hε.2]⟩ ⟨hb0.le, hb1.le⟩ hb0.le
  have h2' : pfun V R Bc Dc γ ξ ε b ≤ pfun V R Bc Dc γ ξ a b :=
    monoA b hb0 hb1 ⟨hε.1.le, by linarith [hε.2]⟩ ⟨ha0.le, ha1.le⟩ hε.2.le
  exact h1.trans h2'

theorem familyR_zero_zero (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (hR0 : ∀ i j l, (i = 0 ∨ i = 5) → (j = 0 ∨ j = 5) → R i j l = 0) (γ : ℝ) :
    familyR R γ 0 0 = 0 := by
  unfold familyR DelaunayStretch.bernstein
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro l _
  by_cases hi : (i : ℕ) = 0
  · by_cases hj : (j : ℕ) = 0
    · have : R i j l = 0 := hR0 i j l (Or.inl (Fin.ext hi)) (Or.inl (Fin.ext hj))
      simp [this]
    · simp [zero_pow hj]
  · simp [zero_pow hi]

theorem bernstein_one_sub (d i : ℕ) (hi : i ≤ d) (x : ℝ) :
    DelaunayStretch.bernstein d i (1 - x) = DelaunayStretch.bernstein d (d - i) x := by
  unfold DelaunayStretch.bernstein
  rw [Nat.choose_symm hi, Nat.sub_sub_self hi]; ring

theorem familyV_reflect (V : Fin 12 → Fin 12 → Fin 35 → ℚ)
    (hV : ∀ i j l, V (Fin.rev i) (Fin.rev j) l = -V i j l) (γ a b : ℝ) :
    familyV V γ (1 - a) (1 - b) = -familyV V γ a b := by
  unfold familyV
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro l _
  simp only [Fin.revPerm_apply]
  rw [bernstein_one_sub 11 _ (by omega), bernstein_one_sub 11 _ (by omega), hV]
  simp only [Fin.val_rev, Rat.cast_neg]
  have e1 : 11 - (12 - ((i : ℕ) + 1)) = i := by omega
  have e2 : 11 - (12 - ((j : ℕ) + 1)) = j := by omega
  rw [e1, e2]; ring

theorem familyR_reflect (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (hR : ∀ i j l, R (Fin.rev i) (Fin.rev j) l = R i j l) (γ a b : ℝ) :
    familyR R γ (1 - a) (1 - b) = familyR R γ a b := by
  unfold familyR
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  simp only [Fin.revPerm_apply]
  rw [bernstein_one_sub 5 _ (by omega), bernstein_one_sub 5 _ (by omega), hR]
  simp only [Fin.val_rev]
  have e1 : 5 - (6 - ((i : ℕ) + 1)) = i := by omega
  have e2 : 5 - (6 - ((j : ℕ) + 1)) = j := by omega
  rw [e1, e2]

theorem clip_neg (x : ℝ) : clip 1 (-x) = -clip 1 x := by
  unfold clip
  rcases le_total x 1 with h | h <;> rcases le_total (-1) x with h' | h'
  · rw [min_eq_right (by linarith : -x ≤ 1), max_eq_right (by linarith : (-1:ℝ) ≤ -x),
      min_eq_right h, max_eq_right h']
  · rw [min_eq_left (by linarith : (1:ℝ) ≤ -x), max_eq_right (by norm_num : (-1:ℝ) ≤ 1),
      min_eq_right h, max_eq_left h']; norm_num
  · rw [min_eq_right (by linarith : -x ≤ 1), max_eq_left (by linarith : -x ≤ -1),
      min_eq_left h, max_eq_right (by norm_num : (-1:ℝ) ≤ 1)]
  · linarith

theorem hpos_reflect2 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) (γ φ θ ψ : ℝ)
    (h1 : Real.pi + 2 * γ ≠ 0) (h2 : Real.pi - 2 * γ ≠ 0) :
    familyHPos V R Bc Dc γ φ θ (-ψ) = -familyHPos V R Bc Dc γ (-φ) (Real.pi - θ) ψ := by
  have ea : (Real.pi - θ - -φ + γ) / (Real.pi + 2 * γ) = 1 - (θ - φ + γ) / (Real.pi + 2 * γ) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1]; ring
  have eb : (Real.pi - θ + -φ - γ) / (Real.pi - 2 * γ) = 1 - (θ + φ - γ) / (Real.pi - 2 * γ) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h2]; ring
  simp only [familyHPos]
  rw [ea, eb, familyV_reflect V hc.1, familyR_reflect R hc.2.1, neg_div, clip_neg]
  ring

theorem omega_strict (γ φ θ : ℝ) (h : (γ, φ, θ) ∈ OmegaSet) :
    |γ| < Real.pi / 2 ∧ 0 < (θ - φ + γ) / (Real.pi + 2 * γ) ∧ (θ - φ + γ) / (Real.pi + 2 * γ) < 1 ∧
      0 < (θ + φ - γ) / (Real.pi - 2 * γ) ∧ (θ + φ - γ) / (Real.pi - 2 * γ) < 1 := by
  obtain ⟨hg, -⟩ := omega_facts γ φ θ h
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hb1 := le_abs_self (γ - φ); have hb2 := neg_abs_le (γ - φ)
  have hc1 := le_abs_self (γ + φ); have hc2 := neg_abs_le (γ + φ)
  obtain ⟨g1, g2⟩ := abs_lt.mp hg
  have p1 : 0 < Real.pi + 2 * γ := by linarith
  have p2 : 0 < Real.pi - 2 * γ := by linarith
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · apply div_pos _ p1; linarith
  · rw [div_lt_one p1]; linarith
  · apply div_pos _ p2; linarith
  · rw [div_lt_one p2]; linarith

theorem first_ineq (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) (U : ℝ)
    (h2 : ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1)
    (h511 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 →
      Real.pi / 2 - U * Real.cos γ ≤
        Real.cos γ ^ 2 * familyV V γ 0 0 +
          (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * (γ / (Real.pi / 2 - Real.cos γ)) +
          Real.cos γ ^ 2 * (familySpline Bc γ * ((γ / (Real.pi / 2 - Real.cos γ)) -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 3) +
            familySpline Dc γ * ((γ / (Real.pi / 2 - Real.cos γ)) ^ 3 -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 5)))
    (γ φ θ : ℝ) (hΩ : (γ, φ, θ) ∈ OmegaSet) (hγ0 : 0 ≤ γ) :
    Real.pi / 2 - U * Real.cos γ ≤ familyHPos V R Bc Dc γ φ θ γ := by
  obtain ⟨hg, ha0, ha1, hb0, hb1⟩ := omega_strict γ φ θ hΩ
  have hγ : γ < Real.pi / 2 := (abs_lt.mp hg).2
  have hk : 0 < Real.pi / 2 - Real.cos γ := by
    have := Real.cos_le_one γ; have := Real.pi_gt_three; linarith
  have hγk : γ ≤ Real.pi / 2 - Real.cos γ := by
    have := Real.sin_le (by linarith : (0:ℝ) ≤ Real.pi / 2 - γ)
    rw [Real.sin_pi_div_two_sub] at this; linarith
  have hξ0 : 0 ≤ γ / (Real.pi / 2 - Real.cos γ) := div_nonneg hγ0 hk.le
  have hξ1 : γ / (Real.pi / 2 - Real.cos γ) ≤ 1 := (div_le_one hk).mpr hγk
  have hξ : |γ / (Real.pi / 2 - Real.cos γ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hclip : clip 1 (γ / (Real.pi / 2 - Real.cos γ)) = γ / (Real.pi / 2 - Real.cos γ) := by
    unfold clip; rw [min_eq_right hξ1, max_eq_right (by linarith)]
  have e : familyHPos V R Bc Dc γ φ θ γ = pfun V R Bc Dc γ (γ / (Real.pi / 2 - Real.cos γ))
      ((θ - φ + γ) / (Real.pi + 2 * γ)) ((θ + φ - γ) / (Real.pi - 2 * γ)) := by
    simp only [familyHPos, pfun, hclip]
  rw [e]
  refine le_trans ?_ (pfun_corner_le V R Bc Dc h2 γ γ hγ0 hγ hξ _ _ ha0 ha1 hb0 hb1)
  refine (h511 γ hγ0 hγ).trans (le_of_eq ?_)
  simp only [pfun, familyR_zero_zero R hc.2.2.1]
  ring

theorem solution (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) (U : ℝ)
    (h2 : ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1)
    (h511 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 →
      Real.pi / 2 - U * Real.cos γ ≤
        Real.cos γ ^ 2 * familyV V γ 0 0 +
          (γ - Real.cos γ ^ 2 * familyV V γ 0 1) * (γ / (Real.pi / 2 - Real.cos γ)) +
          Real.cos γ ^ 2 * (familySpline Bc γ * ((γ / (Real.pi / 2 - Real.cos γ)) -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 3) +
            familySpline Dc γ * ((γ / (Real.pi / 2 - Real.cos γ)) ^ 3 -
              (γ / (Real.pi / 2 - Real.cos γ)) ^ 5))) :
    CondH3 U (familyH V R Bc Dc) := by
  have second : ∀ γ φ θ : ℝ, (γ, φ, θ) ∈ OmegaSet → 0 ≤ γ →
      familyHPos V R Bc Dc γ φ θ (-γ) ≤ -(Real.pi / 2) + U * Real.cos γ := by
    intro γ φ θ hΩ hγ0
    obtain ⟨hg, -⟩ := omega_facts γ φ θ hΩ
    obtain ⟨g1, g2⟩ := abs_lt.mp hg
    have hΩ' : (γ, -φ, Real.pi - θ) ∈ OmegaSet := by
      obtain ⟨h1, h2⟩ := hΩ
      simp only at h1 h2
      refine ⟨?_, ?_⟩
      · show |γ - -φ| < Real.pi - θ
        rw [sub_neg_eq_add]; linarith
      · show Real.pi - θ < Real.pi - |γ + -φ|
        rw [← sub_eq_add_neg]; linarith
    rw [hpos_reflect2 V R Bc Dc hc γ φ θ γ (by linarith) (by linarith)]
    have := first_ineq V R Bc Dc hc U h2 h511 γ (-φ) (Real.pi - θ) hΩ' hγ0
    linarith
  intro γ φ θ hΩ
  simp only [familyH]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    exact ⟨first_ineq V R Bc Dc hc U h2 h511 γ φ θ hΩ hγ, second γ φ θ hΩ hγ⟩
  · rw [if_neg hγ, if_neg hγ]
    have hΩ' : (-γ, -φ, θ) ∈ OmegaSet := by
      obtain ⟨h1, h2⟩ := hΩ
      refine ⟨?_, ?_⟩
      · show |-γ - -φ| < θ
        rw [show -γ - -φ = -(γ - φ) by ring, abs_neg]; exact h1
      · show θ < Real.pi - |-γ + -φ|
        rw [show -γ + -φ = -(γ + φ) by ring, abs_neg]; exact h2
    have f1 := first_ineq V R Bc Dc hc U h2 h511 (-γ) (-φ) θ hΩ' (by linarith)
    have f2 := second (-γ) (-φ) θ hΩ' (by linarith)
    rw [Real.cos_neg] at f1 f2
    rw [neg_neg] at f2
    exact ⟨f1, by rw [neg_neg]; exact f2⟩
