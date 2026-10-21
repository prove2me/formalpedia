-- Prove2me | solution 1 for FiniteTD.Markov.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:21:26.976231+00:00
-- url     : https://prove2.me/submissions/e1cba7ec-b9b6-4349-bb87-8b9809209f71

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

set_option autoImplicit false
open FiniteTD.Markov
open scoped InnerProductSpace

theorem ftd_abs_inner_le {d : ℕ} (u θ : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ ≤ 1) :
    |⟪u, θ⟫_ℝ| ≤ ‖θ‖ := by
  calc |⟪u, θ⟫_ℝ| ≤ ‖u‖ * ‖θ‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖θ‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _ = ‖θ‖ := one_mul _

theorem ftd_tdDir_norm_le {S : Type} {d : ℕ} (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d))
    (hRw : ∀ s s', |Rw s s'| ≤ rmax) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (θ : EuclideanSpace ℝ (Fin d)) (s s' : S) :
    ‖tdDir γ Rw φ θ s s'‖ ≤ rmax + 2 * ‖θ‖ := by
  unfold tdDir
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := ftd_abs_inner_le (φ s') θ (hφ s')
  have h2 := ftd_abs_inner_le (φ s) θ (hφ s)
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3 := abs_le.mp (hRw s s')
  have hn := norm_nonneg θ
  have h4 : |Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ| ≤ rmax + 2 * ‖θ‖ := by
    rw [abs_le]
    have a1 := mul_nonneg hγ0 (sub_nonneg.mpr h1'.2)
    have a2 := mul_nonneg hγ0 (neg_le_iff_add_nonneg.mp h1'.1)
    have a3 := mul_nonneg (sub_nonneg.mpr hγ1.le) hn
    constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2, h3.1, h3.2]
  calc |Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ| * ‖φ s‖
      ≤ |Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ| * 1 :=
        mul_le_mul_of_nonneg_left (hφ s) (abs_nonneg _)
    _ ≤ rmax + 2 * ‖θ‖ := by rw [mul_one]; exact h4

theorem ftd_stat_sum {S : Type} [Fintype S] (P : S → S → ℝ) (π : S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (f : S → ℝ) :
    (∑ s, ∑ s', π s * P s s' * f s = ∑ s, π s * f s) ∧
    (∑ s, ∑ s', π s * P s s' * f s' = ∑ s, π s * f s) := by
  constructor
  · refine Finset.sum_congr rfl fun s _ => ?_
    have h := hP.2 s
    calc ∑ s', π s * P s s' * f s = (π s * f s) * ∑ s', P s s' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s' _ => by ring
      _ = π s * f s := by rw [h, mul_one]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    calc ∑ s, π s * P s s' * f s' = (∑ s, π s * P s s') * f s' := by rw [Finset.sum_mul]
      _ = π s' * f s' := by rw [hπ.2.2 s']

theorem ftd_inner_gbar {S : Type} [Fintype S] {d : ℕ} (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ)
    (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (x θ : EuclideanSpace ℝ (Fin d)) :
    ⟪x, gbar π P γ Rw φ θ⟫_ℝ = ∑ s, ∑ s', π s * P s s' *
      ((Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ) * ⟪φ s, x⟫_ℝ) := by
  unfold gbar tdDir
  rw [inner_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [inner_smul_right, inner_smul_right, real_inner_comm (φ s) x]

theorem ftd_lemma3 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - γ) * dNormSq π φ (θstar - θ) ≤ ⟪θstar - θ, gbar π P γ Rw φ θ⟫_ℝ := by
  intro θ
  set a : S → ℝ := fun s => ⟪φ s, θstar - θ⟫_ℝ with ha
  have h1 := ftd_inner_gbar π P γ Rw φ (θstar - θ) θ
  have h2 := ftd_inner_gbar π P γ Rw φ (θstar - θ) θstar
  rw [hstar, inner_zero_right] at h2
  have key : ⟪θstar - θ, gbar π P γ Rw φ θ⟫_ℝ =
      ∑ s, ∑ s', π s * P s s' * ((a s - γ * a s') * a s) := by
    rw [h1]
    have e : (∑ s, ∑ s', π s * P s s' *
      ((Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ) * ⟪φ s, θstar - θ⟫_ℝ)) =
      (∑ s, ∑ s', π s * P s s' *
      ((Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ) * ⟪φ s, θstar - θ⟫_ℝ)) -
      (∑ s, ∑ s', π s * P s s' *
      ((Rw s s' + γ * ⟪φ s', θstar⟫_ℝ - ⟪φ s, θstar⟫_ℝ) * ⟪φ s, θstar - θ⟫_ℝ)) := by
      rw [← h2]; ring
    rw [e, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [ha, inner_sub_right]
    ring
  rw [key]
  have hA := (ftd_stat_sum P π hP hπ (fun s => a s ^ 2)).1
  have hB := (ftd_stat_sum P π hP hπ (fun s => a s ^ 2)).2
  have hD : dNormSq π φ (θstar - θ) = ∑ s, π s * a s ^ 2 := rfl
  rw [hD]
  have e2 : (∑ s, ∑ s', π s * P s s' * (a s ^ 2 - γ / 2 * (a s' ^ 2 + a s ^ 2))) =
      (∑ s, ∑ s', π s * P s s' * a s ^ 2) -
        γ / 2 * ((∑ s, ∑ s', π s * P s s' * a s' ^ 2) + (∑ s, ∑ s', π s * P s s' * a s ^ 2)) := by
    have ee : ∀ s s', π s * P s s' * (a s ^ 2 - γ / 2 * (a s' ^ 2 + a s ^ 2)) =
        π s * P s s' * a s ^ 2 - γ / 2 * (π s * P s s' * a s' ^ 2 + π s * P s s' * a s ^ 2) :=
      fun _ _ => by ring
    simp only [ee, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hle : (∑ s, ∑ s', π s * P s s' * (a s ^ 2 - γ / 2 * (a s' ^ 2 + a s ^ 2))) ≤
      ∑ s, ∑ s', π s * P s s' * ((a s - γ * a s') * a s) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hπ.1 s) (hP.1 s s'))
    nlinarith [mul_nonneg hγ0 (sq_nonneg (a s' - a s))]
  have e3 : (1 - γ) * ∑ s, π s * a s ^ 2 = (∑ s, ∑ s', π s * P s s' * a s ^ 2) -
        γ / 2 * ((∑ s, ∑ s', π s * P s s' * a s' ^ 2) + (∑ s, ∑ s', π s * P s s' * a s ^ 2)) := by
    rw [hA, hB]; ring
  linarith

theorem ftd_projBall_norm_le {d : ℕ} (R : ℝ) (hR : 0 ≤ R) (v : EuclideanSpace ℝ (Fin d)) :
    ‖projBall R v‖ ≤ R := by
  unfold projBall
  split_ifs with h
  · exact h
  · push_neg at h
    have hpos : 0 < ‖v‖ := lt_of_le_of_lt hR h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hpos.le),
      div_mul_cancel₀ _ hpos.ne']

theorem ftd_projBall_nonexp {d : ℕ} (R : ℝ) (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ ≤ R) :
    ‖u - projBall R v‖ ≤ ‖u - v‖ := by
  unfold projBall
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have hR : 0 ≤ R := (norm_nonneg _).trans hu
    have hpos : 0 < ‖v‖ := lt_of_le_of_lt hR h
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = R / ‖v‖ := ⟨_, rfl⟩
    rw [← hc]
    have hcn : c * ‖v‖ = R := by rw [hc]; exact div_mul_cancel₀ _ hpos.ne'
    have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg hR hpos.le
    have hc1 : c ≤ 1 := by rw [hc, div_le_one hpos]; exact h.le
    have hi : ⟪u, v⟫_ℝ ≤ c * ‖v‖ ^ 2 := by
      have := real_inner_le_norm u v
      have h2 : ‖u‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      rw [← hcn] at h2
      nlinarith
    have key : ‖u - c • v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hi),
        mul_nonneg (sq_nonneg (1 - c)) (sq_nonneg ‖v‖)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp key

theorem ftd_ptd_norm_le {S : Type} {d : ℕ} (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR0 : 0 ≤ R) (α : ℕ → ℝ)
    (θ0 : EuclideanSpace ℝ (Fin d)) (hθ0 : ‖θ0‖ ≤ R) (w : ℕ → S) (t : ℕ) :
    ‖ptd γ Rw φ R α θ0 w t‖ ≤ R := by
  cases t with
  | zero => exact hθ0
  | succ n => exact ftd_projBall_norm_le R hR0 _

theorem ftd_lemma8 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ)
    (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R)
    (hα : ∀ t, 0 ≤ α t) :
    ∀ (w : ℕ → S) (t : ℕ),
      ‖θstar - ptd γ Rw φ R α θ0 w (t + 1)‖ ^ 2 ≤
        ‖θstar - ptd γ Rw φ R α θ0 w t‖ ^ 2
          - 2 * α t * (1 - γ) * dNormSq π φ (θstar - ptd γ Rw φ R α θ0 w t)
          + 2 * α t * zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 w t) (w t) (w (t + 1))
          + α t ^ 2 * (rmax + 2 * R) ^ 2 := by
  intro w t
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hbd := ftd_ptd_norm_le γ Rw φ R hR0 α θ0 hθ0 w t
  have hstep : ptd γ Rw φ R α θ0 w (t + 1) = projBall R (ptd γ Rw φ R α θ0 w t +
      α t • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w t) (w t) (w (t + 1))) := rfl
  rw [hstep]
  generalize ptd γ Rw φ R α θ0 w t = θ at hbd ⊢
  generalize hg : tdDir γ Rw φ θ (w t) (w (t + 1)) = g
  have hne := ftd_projBall_nonexp R θstar (θ + α t • g) hR
  have hsq : ‖θstar - projBall R (θ + α t • g)‖ ^ 2 ≤ ‖θstar - (θ + α t • g)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hne 2
  have hexp : ‖θstar - (θ + α t • g)‖ ^ 2 =
      ‖θstar - θ‖ ^ 2 - 2 * α t * ⟪θstar - θ, g⟫_ℝ + α t ^ 2 * ‖g‖ ^ 2 := by
    have : θstar - (θ + α t • g) = (θstar - θ) - α t • g := by abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hgn : ‖g‖ ≤ rmax + 2 * R := by
    rw [← hg]
    exact (ftd_tdDir_norm_le Rw rmax γ φ hRw hγ0 hγ1 hφ θ (w t) (w (t + 1))).trans
      (by linarith)
  have hg2 : ‖g‖ ^ 2 ≤ (rmax + 2 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgn 2
  have hζ : ⟪θstar - θ, g⟫_ℝ = ⟪θstar - θ, gbar π P γ Rw φ θ⟫_ℝ -
      zeta π P γ Rw φ θstar θ (w t) (w (t + 1)) := by
    unfold zeta
    rw [hg]
    have h1 : ⟪θstar - θ, g - gbar π P γ Rw φ θ⟫_ℝ =
        -⟪g - gbar π P γ Rw φ θ, θ - θstar⟫_ℝ := by
      rw [← neg_sub θ θstar, inner_neg_left, real_inner_comm]
    rw [inner_sub_right] at h1
    linarith
  have h3 := ftd_lemma3 P π Rw γ φ θstar hP hπ hγ0 hγ1 hstar θ
  have h4 := mul_le_mul_of_nonneg_left h3 (hα t)
  have h5 := mul_le_mul_of_nonneg_left hg2 (sq_nonneg (α t))
  rw [hexp] at hsq
  rw [hζ] at hsq
  nlinarith

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ)
    (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R)
    (hα : ∀ t, 0 ≤ α t) :
    ∀ (w : ℕ → S) (t : ℕ),
      ‖θstar - ptd γ Rw φ R α θ0 w (t + 1)‖ ^ 2 ≤
        ‖θstar - ptd γ Rw φ R α θ0 w t‖ ^ 2
          - 2 * α t * (1 - γ) * dNormSq π φ (θstar - ptd γ Rw φ R α θ0 w t)
          + 2 * α t * zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 w t) (w t) (w (t + 1))
          + α t ^ 2 * (rmax + 2 * R) ^ 2 :=
  ftd_lemma8 P π Rw rmax γ φ R α θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hR hθ0 hα
