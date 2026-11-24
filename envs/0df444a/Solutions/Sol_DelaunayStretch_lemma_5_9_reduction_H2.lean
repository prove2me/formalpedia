-- Prove2me | solution 1 for DelaunayStretch.lemma_5_9_reduction_H2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:22:58.797504+00:00
-- url     : https://prove2.me/submissions/06fe4856-7ed4-49d9-b5d7-974d51c4d4fb

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch

namespace L59

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

end L59

open L59

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

theorem piece_ineq (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ)
    (hmono : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∀ s : ℝ, (s = 2 / 5 ∨ s = -(2 / 5)) →
        0 ≤ deriv (fun a' => familyV V γ a' b + s * familyR R γ a' b) a ∧
        0 ≤ deriv (fun b' => familyV V γ a b' + s * familyR R γ a b') b)
    (F : R4 → ℝ) (X : ℝ → ℝ → ℝ)
    (hF : ∀ w : R4, F w = familyHhat V R Bc Dc w.1 (posA w) (posB w) (X w.1 w.2.2.2))
    (z : R4) (hz : z ∈ OmegaTimesR) (hγ : 0 ≤ z.1) (hX : |X z.1 z.2.2.2| ≤ 1) :
    |(gradient4 F z).2.1| ≤ (gradient4 F z).2.2.1 := by
  obtain ⟨hg, ha0, ha1, hb0, hb1⟩ := omega_facts z.1 z.2.1 z.2.2.1 hz
  have hγ2 : z.1 < Real.pi / 2 := (abs_lt.mp hg).2
  have p1 : 0 < Real.pi + 2 * z.1 := by have := Real.pi_pos; linarith
  have p2 : 0 < Real.pi - 2 * z.1 := by linarith
  set ξ := X z.1 z.2.2.2
  have hχ := chi_bound ξ hX
  have hmA := hmono z.1 (posA z) (posB z) hγ hγ2.le ha0 ha1 hb0 hb1
  have hc2 : 0 ≤ Real.cos z.1 ^ 2 := sq_nonneg _
  refine grad_ineq_of_dirs F z
    (Real.cos z.1 ^ 2 * (2 / (Real.pi + 2 * z.1)) * (deriv (fun a' => familyV V z.1 a' (posB z)) (posA z) +
      (ξ - ξ ^ 3) * deriv (fun a' => familyR R z.1 a' (posB z)) (posA z)))
    (Real.cos z.1 ^ 2 * (2 / (Real.pi - 2 * z.1)) * (deriv (fun b' => familyV V z.1 (posA z) b') (posB z) +
      (ξ - ξ ^ 3) * deriv (fun b' => familyR R z.1 (posA z) b') (posB z))) ?_ ?_ ?_ ?_
  · have e : (fun t => F (z.1, z.2.1 - t, z.2.2.1 + t, z.2.2.2)) =
        fun t => familyHhat V R Bc Dc z.1 (posA z + 2 / (Real.pi + 2 * z.1) * t) (posB z) ξ := by
      funext t; rw [hF]; simp only [posA, posB]; congr 2
      · field_simp; ring
      · ring_nf
    rw [e]; exact hhat_deriv_a V R Bc Dc z.1 (posA z) (posB z) ξ _ hγ
  · apply mul_nonneg (mul_nonneg hc2 (by positivity))
    have h1 := (hmA (2/5) (Or.inl rfl)).1
    have h2 := (hmA (-(2/5)) (Or.inr rfl)).1
    rw [deriv_comb_a] at h1 h2
    exact mix_nonneg _ _ _ hχ h1 h2
  · have e : (fun t => F (z.1, z.2.1 + t, z.2.2.1 + t, z.2.2.2)) =
        fun t => familyHhat V R Bc Dc z.1 (posA z) (posB z + 2 / (Real.pi - 2 * z.1) * t) ξ := by
      funext t; rw [hF]; simp only [posA, posB]; congr 2
      · ring_nf
      · field_simp; ring
    rw [e]; exact hhat_deriv_b V R Bc Dc z.1 (posA z) (posB z) ξ _ hγ
  · apply mul_nonneg (mul_nonneg hc2 (by positivity))
    have h1 := (hmA (2/5) (Or.inl rfl)).2
    have h2 := (hmA (-(2/5)) (Or.inr rfl)).2
    rw [deriv_comb_b] at h1 h2
    exact mix_nonneg _ _ _ hχ h1 h2

theorem solution (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ)
    (hmono : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∀ s : ℝ, (s = 2 / 5 ∨ s = -(2 / 5)) →
        0 ≤ deriv (fun a' => familyV V γ a' b + s * familyR R γ a' b) a ∧
        0 ≤ deriv (fun b' => familyV V γ a b' + s * familyR R γ a b') b) :
    ∀ z g : R4, IsPieceGradient V R Bc Dc z g → |g.2.1| ≤ g.2.2.1 := by
  rintro z g ⟨hz, hγ, h | h | h⟩
  · obtain ⟨hξ, rfl⟩ := h
    exact piece_ineq V R Bc Dc hmono _ (fun γ ψ => ψ / (Real.pi / 2 - Real.cos γ))
      (fun w => rfl) z hz hγ hξ
  · obtain ⟨-, rfl⟩ := h
    exact piece_ineq V R Bc Dc hmono _ (fun _ _ => 1) (fun w => rfl) z hz hγ (by norm_num)
  · obtain ⟨-, rfl⟩ := h
    exact piece_ineq V R Bc Dc hmono _ (fun _ _ => -1) (fun w => rfl) z hz hγ (by norm_num)
