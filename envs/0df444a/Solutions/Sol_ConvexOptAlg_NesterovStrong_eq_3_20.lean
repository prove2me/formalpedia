-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.eq_3_20
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:45:28.937305+00:00
-- url     : https://prove2.me/submissions/6ea445f0-19b1-4cb1-add2-c22a8e0b6e8a

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs
set_option autoImplicit false

open scoped InnerProductSpace
open ConvexOptAlg.NesterovStrong

private lemma phi_canonical {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ) (hs : 1 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x s z = PhiStar f g α β x s + α / 2 * ‖z - v g α β x s‖ ^ 2 := by
  induction s, hs using Nat.le_induction generalizing z with
  | base =>
    simp [PhiStar, Phi, v]
  | succ s hs ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
    have h_phi_z : Phi f g α β x (k + 2) z =
        (1 - 1 / Real.sqrt (kappa α β)) * Phi f g α β x (k + 1) z +
          1 / Real.sqrt (kappa α β) *
            (f (x (k + 1)) + ⟪g (x (k + 1)), z - x (k + 1)⟫_ℝ + α / 2 * ‖z - x (k + 1)‖ ^ 2) := rfl
    let vn := v g α β x (k + 2)
    let vk := v g α β x (k + 1)
    let xk := x (k + 1)
    let gk := g (x (k + 1))
    let γ := 1 / Real.sqrt (kappa α β)
    let c := 1 / (α * Real.sqrt (kappa α β))
    have hvn_def : vn = (1 - γ) • vk + γ • xk - c • gk := rfl
    have h_pstar : PhiStar f g α β x (k + 2) =
        (1 - γ) * Phi f g α β x (k + 1) vn +
          γ * (f xk + ⟪gk, vn - xk⟫_ℝ + α / 2 * ‖vn - xk‖ ^ 2) := rfl
    rw [h_phi_z, h_pstar, ih z, ih vn]
    let w := z - vn
    have hz_vk : z - vk = (vn - vk) + w := by dsimp [w]; abel
    have hz_xk : z - xk = (vn - xk) + w := by dsimp [w]; abel
    have h_norm_vk : ‖z - vk‖ ^ 2 = ‖vn - vk‖ ^ 2 + 2 * ⟪vn - vk, w⟫_ℝ + ‖w‖ ^ 2 := by
      rw [hz_vk, norm_add_sq_real]
    have h_norm_xk : ‖z - xk‖ ^ 2 = ‖vn - xk‖ ^ 2 + 2 * ⟪vn - xk, w⟫_ℝ + ‖w‖ ^ 2 := by
      rw [hz_xk, norm_add_sq_real]
    have h_inner_gk : ⟪gk, z - xk⟫_ℝ = ⟪gk, vn - xk⟫_ℝ + ⟪gk, w⟫_ℝ := by
      rw [hz_xk, inner_add_right]
    have h_lin_vec : α • ((1 - γ) • (vn - vk) + γ • (vn - xk)) + γ • gk = 0 := by
      have h_comb : α • ((1 - γ) • (vn - vk) + γ • (vn - xk)) + γ • gk =
          (γ - α * c) • gk := by
        rw [hvn_def]
        module
      have h_coeff : γ - α * c = 0 := by
        dsimp [γ, c]
        have hα0 : α ≠ 0 := hα.ne'
        field_simp
        ring
      rw [h_comb, h_coeff, zero_smul]
    have h_lin : α * (1 - γ) * ⟪vn - vk, w⟫_ℝ + α * γ * ⟪vn - xk, w⟫_ℝ + γ * ⟪gk, w⟫_ℝ = 0 := by
      have h0 : ⟪α • ((1 - γ) • (vn - vk) + γ • (vn - xk)) + γ • gk, w⟫_ℝ = 0 := by
        rw [h_lin_vec, inner_zero_left]
      simpa [inner_add_left, real_inner_smul_left, mul_add, mul_assoc] using h0
    change (1 - γ) * (PhiStar f g α β x (k + 1) + α / 2 * ‖z - vk‖ ^ 2) +
        γ * (f xk + ⟪gk, z - xk⟫_ℝ + α / 2 * ‖z - xk‖ ^ 2) =
      (1 - γ) * (PhiStar f g α β x (k + 1) + α / 2 * ‖vn - vk‖ ^ 2) +
        γ * (f xk + ⟪gk, vn - xk⟫_ℝ + α / 2 * ‖vn - xk‖ ^ 2) + α / 2 * ‖w‖ ^ 2
    rw [h_norm_vk, h_norm_xk, h_inner_gk]
    linarith

private lemma v_coupling {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) :
    v g α β x s - x s = Real.sqrt (kappa α β) • (x s - y s) := by
  have hκ_pos : 0 < kappa α β := div_pos hβ hα
  let q := Real.sqrt (kappa α β)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr hκ_pos
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq1_ne : q + 1 ≠ 0 := by linarith
  have hq_sq : q ^ 2 = β / α := Real.sq_sqrt hκ_pos.le
  induction s, hs using Nat.le_induction with
  | base =>
    change v g α β x 1 - x 1 = q • (x 1 - y 1)
    rw [v, hrun.1, sub_self, smul_zero]
  | succ s hs ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
    rcases hrun.2 (k + 1) hs with ⟨hy_next, hx_next⟩
    have hv_next : v g α β x (k + 2) =
        (1 - 1 / q) • v g α β x (k + 1) + (1 / q) • x (k + 1) -
          (1 / (α * q)) • g (x (k + 1)) := rfl
    have hv_curr : v g α β x (k + 1) = x (k + 1) + q • (x (k + 1) - y (k + 1)) :=
      eq_add_of_sub_eq' ih
    have h_diff : (v g α β x (k + 2) - x (k + 2)) - q • (x (k + 2) - y (k + 2)) =
        (((1 - 1 / q) * (1 + q) + 1 / q - (1 + q) * (1 + (q - 1) / (q + 1)) + q) • x (k + 1)) +
        ((-(1 - 1 / q) * q + (1 + q) * ((q - 1) / (q + 1))) • y (k + 1)) +
        ((-1 / (α * q) + (1 + q) * (1 + (q - 1) / (q + 1)) * (1 / β) - q * (1 / β)) •
          g (x (k + 1))) := by
      rw [hv_next, hv_curr, hx_next, hy_next]
      module
    have hc1 : (1 - 1 / q) * (1 + q) + 1 / q - (1 + q) * (1 + (q - 1) / (q + 1)) + q = 0 := by
      field_simp
      ring
    have hc2 : -(1 - 1 / q) * q + (1 + q) * ((q - 1) / (q + 1)) = 0 := by
      field_simp
      ring
    have hc3 : -1 / (α * q) + (1 + q) * (1 + (q - 1) / (q + 1)) * (1 / β) - q * (1 / β) = 0 := by
      have hα_ne : α ≠ 0 := hα.ne'
      have hβ_ne : β ≠ 0 := hβ.ne'
      have hβ_eq : β = α * q ^ 2 := by
        rw [hq_sq]
        field_simp
      rw [hβ_eq]
      field_simp
      ring
    rw [hc1, hc2, hc3, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at h_diff
    exact sub_eq_zero.mp h_diff

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) :
    PhiStar f g α β x (s + 1) ≥
      (1 - 1 / Real.sqrt (kappa α β)) * PhiStar f g α β x s +
        (1 - 1 / Real.sqrt (kappa α β)) * ⟪g (x s), x s - y s⟫_ℝ +
          1 / Real.sqrt (kappa α β) * f (x s) - 1 / (2 * β) * ‖g (x s)‖ ^ 2 := by
  by_cases hn : 0 < n
  · have h_le_αβ : α ≤ β := by
      let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
      have hu_pos : 0 < ‖u‖ := by
        rw [norm_pos_iff]
        intro hu0
        have : u ⟨0, hn⟩ = 0 := by rw [hu0]; rfl
        norm_num [u] at this
      have h1 := hsc 0 trivial u trivial
      have h2 := hsc u trivial 0 trivial
      have h_add : α * ‖u‖ ^ 2 ≤ ⟪g u - g 0, u⟫_ℝ := by
        have : ⟪g u - g 0, u⟫_ℝ = -⟪g u, 0 - u⟫_ℝ - ⟪g 0, u - 0⟫_ℝ := by
          rw [inner_sub_left, sub_zero, zero_sub, inner_neg_right]
          ring
        have h_u0 : ‖u - 0‖ = ‖u‖ := by rw [sub_zero]
        rw [norm_sub_rev 0 u, h_u0] at h2
        rw [h_u0] at h1
        linarith
      have h_cs : ⟪g u - g 0, u⟫_ℝ ≤ β * ‖u‖ ^ 2 := by
        calc ⟪g u - g 0, u⟫_ℝ ≤ ‖g u - g 0‖ * ‖u‖ := real_inner_le_norm _ _
          _ ≤ (β * ‖u - 0‖) * ‖u‖ := mul_le_mul_of_nonneg_right (hsm.2 u 0) (norm_nonneg u)
          _ = β * ‖u‖ ^ 2 := by rw [sub_zero]; ring
      nlinarith [sq_pos_of_pos hu_pos]
    let q := Real.sqrt (kappa α β)
    have hκ_ge1 : 1 ≤ kappa α β := (one_le_div hα).mpr h_le_αβ
    have hq_ge1 : 1 ≤ q := Real.one_le_sqrt.mpr hκ_ge1
    have hq_pos : 0 < q := by linarith
    have hq_ne : q ≠ 0 := hq_pos.ne'
    have hq_sq : q ^ 2 = β / α := Real.sq_sqrt (by positivity)
    let γ := 1 / q
    have hγ_pos : 0 < γ := by positivity
    have h1mγ_nonneg : 0 ≤ 1 - γ := by
      dsimp [γ]
      rw [sub_nonneg, div_le_iff₀ hq_pos]
      linarith
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
    have h_can_next := phi_canonical f g α β hα x (k + 2) (by omega) (x (k + 1))
    have h_can_curr := phi_canonical f g α β hα x (k + 1) hs (x (k + 1))
    have h_phi_def : Phi f g α β x (k + 2) (x (k + 1)) =
        (1 - γ) * Phi f g α β x (k + 1) (x (k + 1)) +
          γ * (f (x (k + 1)) + ⟪g (x (k + 1)), x (k + 1) - x (k + 1)⟫_ℝ +
            α / 2 * ‖x (k + 1) - x (k + 1)‖ ^ 2) := rfl
    rw [sub_self, inner_zero_right, norm_zero] at h_phi_def
    have hv_step : x (k + 1) - v g α β x (k + 2) =
        (1 - γ) • (x (k + 1) - v g α β x (k + 1)) +
          (1 / (α * q)) • g (x (k + 1)) := by
      change x (k + 1) - ((1 - γ) • v g α β x (k + 1) + γ • x (k + 1) -
        (1 / (α * q)) • g (x (k + 1))) = _
      module
    have h_norm_expand : ‖x (k + 1) - v g α β x (k + 2)‖ ^ 2 =
        (1 - γ) ^ 2 * ‖x (k + 1) - v g α β x (k + 1)‖ ^ 2 +
          2 * (1 - γ) * (1 / (α * q)) * ⟪g (x (k + 1)), x (k + 1) - v g α β x (k + 1)⟫_ℝ +
          (1 / (α * q)) ^ 2 * ‖g (x (k + 1))‖ ^ 2 := by
      rw [hv_step, norm_add_sq_real, norm_smul, norm_smul,
        Real.norm_of_nonneg h1mγ_nonneg, Real.norm_of_nonneg (by positivity),
        real_inner_smul_left, real_inner_smul_right,
        real_inner_comm (x (k + 1) - v g α β x (k + 1))]
      ring
    have h_coup := v_coupling g α β hα hβ x y hrun (k + 1) hs
    have h_xv : x (k + 1) - v g α β x (k + 1) = -(q • (x (k + 1) - y (k + 1))) := by
      rw [← h_coup, neg_sub]
    have h_inner_coup : ⟪g (x (k + 1)), x (k + 1) - v g α β x (k + 1)⟫_ℝ =
        -q * ⟪g (x (k + 1)), x (k + 1) - y (k + 1)⟫_ℝ := by
      rw [h_xv, inner_neg_right, real_inner_smul_right]
      ring
    have hα_ne : α ≠ 0 := hα.ne'
    have hβ_ne : β ≠ 0 := hβ.ne'
    have hβ_eq : β = α * q ^ 2 := by rw [hq_sq]; field_simp
    have h_alg1 : α / 2 * (2 * (1 - γ) * (1 / (α * q)) * (-q)) = -(1 - γ) := by
      field_simp
    have h_alg2 : α / 2 * (1 / (α * q)) ^ 2 = 1 / (2 * β) := by
      rw [hβ_eq]
      field_simp
    have h_nonneg_term : 0 ≤ α / 2 * ((1 - γ) - (1 - γ) ^ 2) *
        ‖x (k + 1) - v g α β x (k + 1)‖ ^ 2 := by
      have : (1 - γ) - (1 - γ) ^ 2 = (1 - γ) * γ := by ring
      rw [this]
      positivity
    have h_eq_pstar : PhiStar f g α β x (k + 2) =
        (1 - γ) * PhiStar f g α β x (k + 1) +
          (1 - γ) * ⟪g (x (k + 1)), x (k + 1) - y (k + 1)⟫_ℝ +
          γ * f (x (k + 1)) - 1 / (2 * β) * ‖g (x (k + 1))‖ ^ 2 +
          α / 2 * ((1 - γ) - (1 - γ) ^ 2) * ‖x (k + 1) - v g α β x (k + 1)‖ ^ 2 := by
      have h_comb : PhiStar f g α β x (k + 2) + α / 2 * ‖x (k + 1) - v g α β x (k + 2)‖ ^ 2 =
          (1 - γ) * (PhiStar f g α β x (k + 1) + α / 2 * ‖x (k + 1) - v g α β x (k + 1)‖ ^ 2) +
            γ * f (x (k + 1)) := by
        rw [h_can_next, h_can_curr] at h_phi_def
        linear_combination h_phi_def
      rw [h_norm_expand, h_inner_coup] at h_comb
      linear_combination h_comb - ⟪g (x (k + 1)), x (k + 1) - y (k + 1)⟫_ℝ * h_alg1 -
        ‖g (x (k + 1))‖ ^ 2 * h_alg2
    change PhiStar f g α β x (k + 2) ≥
      (1 - γ) * PhiStar f g α β x (k + 1) +
        (1 - γ) * ⟪g (x (k + 1)), x (k + 1) - y (k + 1)⟫_ℝ +
          γ * f (x (k + 1)) - 1 / (2 * β) * ‖g (x (k + 1))‖ ^ 2
    linarith
  · have h_sub : ∀ u w : EuclideanSpace ℝ (Fin n), u = w := fun u w => by
      ext i
      exact False.elim (hn (Nat.zero_lt_of_lt i.isLt))
    have h_phi_const : ∀ m : ℕ, 1 ≤ m → ∀ z, Phi f g α β x m z = f (x 1) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro z
        simp [Phi, h_sub z (x 1)]
      | succ m hm ih =>
        intro z
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
        change (1 - 1 / Real.sqrt (kappa α β)) * Phi f g α β x (k + 1) z +
          1 / Real.sqrt (kappa α β) * (f (x (k + 1)) +
            ⟪g (x (k + 1)), z - x (k + 1)⟫_ℝ + α / 2 * ‖z - x (k + 1)‖ ^ 2) = f (x 1)
        rw [ih z, h_sub (x (k + 1)) (x 1), h_sub z (x 1), sub_self, inner_zero_right, norm_zero]
        ring
    rw [PhiStar, PhiStar, h_phi_const (s + 1) (by omega), h_phi_const s hs,
      h_sub (x s) (x 1), h_sub (y s) (x 1), h_sub (g (x 1)) 0, sub_self, inner_zero_left,
      norm_zero]
    linarith
