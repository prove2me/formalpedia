-- Prove2me | solution 1 for FiniteTD.Markov.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:37:00.964908+00:00
-- url     : https://prove2.me/submissions/d302a3df-3ded-4829-8d66-d531128875ca

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

theorem ftd_wsum_norm_le {S : Type} [Fintype S] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : S → S → ℝ) (π : S → ℝ) (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (F : S → S → E) (B : ℝ) (hF : ∀ s s', ‖F s s'‖ ≤ B) :
    ‖∑ s, ∑ s', (π s * P s s') • F s s'‖ ≤ B := by
  calc ‖∑ s, ∑ s', (π s * P s s') • F s s'‖ ≤ ∑ s, ‖∑ s', (π s * P s s') • F s s'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ s, ∑ s', ‖(π s * P s s') • F s s'‖ := Finset.sum_le_sum fun s _ => norm_sum_le _ _
    _ ≤ ∑ s, ∑ s', π s * P s s' * B := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
        have hw : 0 ≤ π s * P s s' := mul_nonneg (hπ.1 s) (hP.1 s s')
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hF s s') hw
    _ = ∑ s, π s * B := (ftd_stat_sum P π hP hπ (fun _ => B)).1
    _ = B := by rw [← Finset.sum_mul, hπ.2.1, one_mul]

theorem ftd_tdDir_sub_norm_le {S : Type} {d : ℕ} (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (θ θ' : EuclideanSpace ℝ (Fin d)) (s s' : S) :
    ‖tdDir γ Rw φ θ s s' - tdDir γ Rw φ θ' s s'‖ ≤ 2 * ‖θ - θ'‖ := by
  have e : tdDir γ Rw φ θ s s' - tdDir γ Rw φ θ' s s' =
      (γ * ⟪φ s', θ - θ'⟫_ℝ - ⟪φ s, θ - θ'⟫_ℝ) • φ s := by
    unfold tdDir
    rw [← sub_smul]
    congr 1
    rw [inner_sub_right, inner_sub_right]
    ring
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := abs_le.mp (ftd_abs_inner_le (φ s') (θ - θ') (hφ s'))
  have h2 := abs_le.mp (ftd_abs_inner_le (φ s) (θ - θ') (hφ s))
  have hn := norm_nonneg (θ - θ')
  have a1 := mul_nonneg hγ0 (sub_nonneg.mpr h1.2)
  have a2 := mul_nonneg hγ0 (neg_le_iff_add_nonneg.mp h1.1)
  have h4 : |γ * ⟪φ s', θ - θ'⟫_ℝ - ⟪φ s, θ - θ'⟫_ℝ| ≤ 2 * ‖θ - θ'‖ := by
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  calc |γ * ⟪φ s', θ - θ'⟫_ℝ - ⟪φ s, θ - θ'⟫_ℝ| * ‖φ s‖
      ≤ |γ * ⟪φ s', θ - θ'⟫_ℝ - ⟪φ s, θ - θ'⟫_ℝ| * 1 :=
        mul_le_mul_of_nonneg_left (hφ s) (abs_nonneg _)
    _ ≤ 2 * ‖θ - θ'‖ := by rw [mul_one]; exact h4

theorem ftd_gbar_norm_le {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (θ : EuclideanSpace ℝ (Fin d)) (B : ℝ) (hB : ∀ s s', ‖tdDir γ Rw φ θ s s'‖ ≤ B) :
    ‖gbar π P γ Rw φ θ‖ ≤ B :=
  ftd_wsum_norm_le P π hP hπ (fun s s' => tdDir γ Rw φ θ s s') B hB

theorem ftd_gbar_sub_norm_le {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (θ θ' : EuclideanSpace ℝ (Fin d)) :
    ‖gbar π P γ Rw φ θ - gbar π P γ Rw φ θ'‖ ≤ 2 * ‖θ - θ'‖ := by
  have e : gbar π P γ Rw φ θ - gbar π P γ Rw φ θ' =
      ∑ s, ∑ s', (π s * P s s') • (tdDir γ Rw φ θ s s' - tdDir γ Rw φ θ' s s') := by
    unfold gbar
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← smul_sub]
  rw [e]
  exact ftd_wsum_norm_le P π hP hπ _ _ (fun s s' => ftd_tdDir_sub_norm_le Rw γ φ hγ0 hγ1 hφ θ θ' s s')

theorem ftd_lemma10 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hR : ‖θstar‖ ≤ R) :
    ∀ (s s' : S) (θ θ' : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ‖θ'‖ ≤ R →
      |zeta π P γ Rw φ θstar θ s s'| ≤ 2 * (rmax + 2 * R) ^ 2 ∧
      |zeta π P γ Rw φ θstar θ s s' - zeta π P γ Rw φ θstar θ' s s'|
        ≤ 6 * (rmax + 2 * R) * ‖θ - θ'‖ := by
  intro s s' θ θ' hθ hθ'
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hrmax : 0 ≤ rmax := (abs_nonneg _).trans (hRw s s')
  have hG : ∀ ϑ : EuclideanSpace ℝ (Fin d), ‖ϑ‖ ≤ R → ∀ a b,
      ‖tdDir γ Rw φ ϑ a b‖ ≤ rmax + 2 * R := fun ϑ hϑ a b =>
    (ftd_tdDir_norm_le Rw rmax γ φ hRw hγ0 hγ1 hφ ϑ a b).trans (by linarith)
  have hgb : ∀ ϑ : EuclideanSpace ℝ (Fin d), ‖ϑ‖ ≤ R → ‖gbar π P γ Rw φ ϑ‖ ≤ rmax + 2 * R :=
    fun ϑ hϑ => ftd_gbar_norm_le P π Rw γ φ hP hπ ϑ _ (hG ϑ hϑ)
  have hh : ∀ ϑ : EuclideanSpace ℝ (Fin d), ‖ϑ‖ ≤ R →
      ‖tdDir γ Rw φ ϑ s s' - gbar π P γ Rw φ ϑ‖ ≤ 2 * (rmax + 2 * R) := fun ϑ hϑ =>
    (norm_sub_le _ _).trans (by linarith [hG ϑ hϑ s s', hgb ϑ hϑ])
  have hGn : 0 ≤ rmax + 2 * R := by linarith
  constructor
  · unfold zeta
    have h1 := abs_real_inner_le_norm (tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) (θ - θstar)
    have h2 : ‖θ - θstar‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    have h3 : ‖tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ‖ * ‖θ - θstar‖ ≤
        (2 * (rmax + 2 * R)) * (2 * R) :=
      mul_le_mul (hh θ hθ) h2 (norm_nonneg _) (by linarith)
    nlinarith [mul_nonneg hrmax hGn]
  · have e : zeta π P γ Rw φ θstar θ s s' - zeta π P γ Rw φ θstar θ' s s' =
        ⟪(tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) - (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ'),
          θ - θstar⟫_ℝ +
        ⟪tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ', θ - θ'⟫_ℝ := by
      unfold zeta
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [e]
    have hΔ := norm_nonneg (θ - θ')
    have hd1 : ‖(tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) -
        (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ')‖ ≤ 4 * ‖θ - θ'‖ := by
      have : (tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) -
        (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ') =
        (tdDir γ Rw φ θ s s' - tdDir γ Rw φ θ' s s') -
          (gbar π P γ Rw φ θ - gbar π P γ Rw φ θ') := by abel
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      linarith [ftd_tdDir_sub_norm_le Rw γ φ hγ0 hγ1 hφ θ θ' s s',
        ftd_gbar_sub_norm_le P π Rw γ φ hP hπ hγ0 hγ1 hφ θ θ']
    have h2 : ‖θ - θstar‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    have t1 := abs_real_inner_le_norm ((tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) -
        (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ')) (θ - θstar)
    have t2 := abs_real_inner_le_norm (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ') (θ - θ')
    have u1 : ‖(tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) -
        (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ')‖ * ‖θ - θstar‖ ≤ (4 * ‖θ - θ'‖) * (2 * R) :=
      mul_le_mul hd1 h2 (norm_nonneg _) (by positivity)
    have u2 : ‖tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ'‖ * ‖θ - θ'‖ ≤
        (2 * (rmax + 2 * R)) * ‖θ - θ'‖ :=
      mul_le_mul_of_nonneg_right (hh θ' hθ') hΔ
    have := abs_add_le
      ⟪(tdDir γ Rw φ θ s s' - gbar π P γ Rw φ θ) - (tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ'),
          θ - θstar⟫_ℝ
      ⟪tdDir γ Rw φ θ' s s' - gbar π P γ Rw φ θ', θ - θ'⟫_ℝ
    nlinarith [mul_nonneg hrmax hΔ]

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

def ftd_pfx {S : Type} (k N : ℕ) (h : k ≤ N) (w : Fin (N + 1) → S) : Fin (k + 1) → S :=
  fun i => w ⟨i.1, by have := i.2; omega⟩

theorem ftd_pfx_snoc {S : Type} (k N : ℕ) (h : k ≤ N) (w : Fin (N + 1) → S) (s : S) :
    ftd_pfx k (N + 1) (by omega) (Fin.snoc (α := fun _ => S) w s : Fin (N + 2) → S) =
      ftd_pfx k N h w := by
  funext i
  unfold ftd_pfx
  exact Fin.snoc_castSucc (α := fun _ => S) s w ⟨i.1, by have := i.2; omega⟩

theorem ftd_pathProb_snoc {S : Type} [Fintype S] (π : S → ℝ) (P : S → S → ℝ) (k : ℕ)
    (w : Fin (k + 1) → S) (s : S) :
    pathProb π P (k + 1) (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) =
      pathProb π P k w * P (w (Fin.last k)) s := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) 0 = w 0 :=
    Fin.snoc_apply_zero (α := fun _ => S) s w
  rw [h0]
  simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

theorem ftd_pathExp_succ {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (k : ℕ) (F : (Fin (k + 2) → S) → ℝ) :
    pathExp π P (k + 1) F = pathExp π P k (fun w => ∑ s,
      P (w (Fin.last k)) s * F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S)) := by
  unfold pathExp
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 2) => S)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  show ∑ s, pathProb π P (k + 1) (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) *
      F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S) =
    pathProb π P k w * ∑ s, P (w (Fin.last k)) s * F (Fin.snoc (α := fun _ => S) w s : Fin (k + 2) → S)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ftd_pathProb_snoc]
  ring

theorem ftd_pathExp_zero {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (F : (Fin 1 → S) → ℝ) : pathExp π P 0 F = ∑ a, π a * F (fun _ => a) := by
  unfold pathExp pathProb
  rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
  simp
  rfl

theorem ftd_pow_row {S : Type} [Fintype S] [DecidableEq S] (P : S → S → ℝ) (hP : IsStochastic P)
    (n : ℕ) (a : S) : ∑ u, (Matrix.of P ^ n) a u = 1 := by
  induction n generalizing a with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ']
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ y, P a i * (Matrix.of P ^ n) i y = ∑ i, P a i * ∑ y, (Matrix.of P ^ n) i y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = 1 := by simp only [ih, mul_one]; exact hP.2 a

theorem ftd_pow_stat {S : Type} [Fintype S] [DecidableEq S] (P : S → S → ℝ) (π : S → ℝ)
    (hπ : IsStationaryDist P π) (n : ℕ) (u : S) :
    ∑ a, π a * (Matrix.of P ^ n) a u = π u := by
  induction n generalizing u with
  | zero =>
    simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    calc ∑ a, π a * ∑ j, (Matrix.of P ^ n) a j * P j u
        = ∑ j, (∑ a, π a * (Matrix.of P ^ n) a j) * P j u := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = ∑ j, π j * P j u := by simp only [ih]
      _ = π u := hπ.2.2 u

theorem ftd_pathProb_nonneg {S : Type} [Fintype S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (w : Fin (k + 1) → S) :
    0 ≤ pathProb π P k w :=
  mul_nonneg (hπ.1 _) (Finset.prod_nonneg fun i _ => hP.1 _ _)

theorem ftd_pathExp_mono {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (F G : (Fin (k + 1) → S) → ℝ)
    (h : ∀ w, F w ≤ G w) : pathExp π P k F ≤ pathExp π P k G :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (ftd_pathProb_nonneg π P hP hπ k w)

theorem ftd_pathExp_const {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (k : ℕ) (c : ℝ) :
    pathExp π P k (fun _ => c) = c := by
  induction k with
  | zero => rw [ftd_pathExp_zero, ← Finset.sum_mul, hπ.2.1, one_mul]
  | succ k ih =>
    rw [ftd_pathExp_succ]
    have : (fun w : Fin (k + 1) → S => ∑ s, P (w (Fin.last k)) s * c) = fun _ => c := by
      funext w
      rw [← Finset.sum_mul, hP.2, one_mul]
    rw [this, ih]

theorem ftd_pathExp_add {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (k : ℕ) (F G : (Fin (k + 1) → S) → ℝ) :
    pathExp π P k (fun w => F w + G w) = pathExp π P k F + pathExp π P k G := by
  unfold pathExp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem ftd_L {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (k : ℕ) :
    ∀ (n : ℕ) (Ψ : (Fin (k + 1) → S) → S → ℝ),
    pathExp π P (k + n) (fun w => Ψ (ftd_pfx k (k + n) (by omega) w) (w (Fin.last (k + n)))) =
      pathExp π P k (fun p => ∑ u, (Matrix.of P ^ n) (p (Fin.last k)) u * Ψ p u) := by
  intro n
  induction n with
  | zero =>
    intro Ψ
    have : ∀ p : Fin (k + 1) → S, ∑ u, (Matrix.of P ^ 0) (p (Fin.last k)) u * Ψ p u =
        Ψ p (p (Fin.last k)) := by
      intro p
      simp [Matrix.one_apply]
    simp only [this]
    rfl
  | succ n ih =>
    intro Ψ
    show pathExp π P ((k + n) + 1) (fun w : Fin ((k + n) + 1 + 1) → S =>
      Ψ (ftd_pfx k ((k + n) + 1) (by omega) w) (w (Fin.last ((k + n) + 1)))) = _
    rw [ftd_pathExp_succ]
    have h1 := ih (fun p u => ∑ s, P u s * Ψ p s)
    have h2 : (fun w : Fin (k + n + 1) → S => ∑ s, P (w (Fin.last (k + n))) s *
        Ψ (ftd_pfx k (k + n + 1) (by omega) (Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S))
          ((Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S) (Fin.last (k + n + 1)))) =
        fun w => (fun p u => ∑ s, P u s * Ψ p s)
          (ftd_pfx k (k + n) (by omega) w) (w (Fin.last (k + n))) := by
      funext w
      simp only [ftd_pfx_snoc k (k + n) (by omega), Fin.snoc_last]
    rw [h2, h1]
    congr 1
    funext p
    rw [pow_succ]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem ftd_marg {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (m j : ℕ) (G : (Fin (m + 1) → S) → ℝ) :
    pathExp π P (m + j) (fun w => G (ftd_pfx m (m + j) (by omega) w)) = pathExp π P m G := by
  have h := ftd_L π P m j (fun p _ => G p)
  rw [h]
  congr 1
  funext p
  rw [← Finset.sum_mul, ftd_pow_row P hP, one_mul]

theorem ftd_W {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (k n : ℕ)
    (Φ : (Fin (k + 1) → S) → S → S → ℝ) :
    pathExp π P (k + n + 1) (fun w => Φ (ftd_pfx k (k + n + 1) (by omega) w)
        (w ⟨k + n, by omega⟩) (w (Fin.last (k + n + 1)))) =
      pathExp π P k (fun p => ∑ u, ∑ u', (Matrix.of P ^ n) (p (Fin.last k)) u * P u u' *
        Φ p u u') := by
  rw [ftd_pathExp_succ]
  have h1 := ftd_L π P k n (fun p u => ∑ s, P u s * Φ p u s)
  have h2 : (fun w : Fin (k + n + 1) → S => ∑ s, P (w (Fin.last (k + n))) s *
      Φ (ftd_pfx k (k + n + 1) (by omega) (Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S))
        ((Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S) ⟨k + n, by omega⟩)
        ((Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S) (Fin.last (k + n + 1)))) =
      fun w => (fun p u => ∑ s, P u s * Φ p u s)
        (ftd_pfx k (k + n) (by omega) w) (w (Fin.last (k + n))) := by
    funext w
    have e : ∀ s : S, (Fin.snoc (α := fun _ => S) w s : Fin (k + n + 2) → S) ⟨k + n, by omega⟩ =
        w (Fin.last (k + n)) := fun s =>
      Fin.snoc_castSucc (α := fun _ => S) s w (Fin.last (k + n))
    simp only [ftd_pfx_snoc k (k + n) (by omega), Fin.snoc_last, e]
  rw [h2, h1]
  congr 1
  funext p
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem ftd_ext_apply {S : Type} {T : ℕ} (w : Fin (T + 1) → S) (i : ℕ) (h : i ≤ T) :
    extendPath w i = w ⟨i, by omega⟩ := by
  unfold extendPath
  congr 1
  exact Fin.ext (min_eq_left h)

theorem ftd_ptd_congr {S : Type} {d : ℕ} (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ) (θ0 : EuclideanSpace ℝ (Fin d))
    (w w' : ℕ → S) (t : ℕ) (h : ∀ i ≤ t, w i = w' i) :
    ptd γ Rw φ R α θ0 w t = ptd γ Rw φ R α θ0 w' t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    show projBall R (ptd γ Rw φ R α θ0 w n +
        α n • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w n) (w n) (w (n + 1))) =
      projBall R (ptd γ Rw φ R α θ0 w' n +
        α n • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w' n) (w' n) (w' (n + 1)))
    rw [ih (fun i hi => h i (by omega)), h n (by omega), h (n + 1) le_rfl]

theorem ftd_ptd_step {S : Type} {d : ℕ} (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR0 : 0 ≤ R) (α : ℕ → ℝ)
    (θ0 : EuclideanSpace ℝ (Fin d)) (hθ0 : ‖θ0‖ ≤ R)
    (hRw : ∀ s s', |Rw s s'| ≤ rmax) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (w : ℕ → S) (i : ℕ) (hα : 0 ≤ α i) :
    ‖ptd γ Rw φ R α θ0 w (i + 1) - ptd γ Rw φ R α θ0 w i‖ ≤ α i * (rmax + 2 * R) := by
  have hbd := ftd_ptd_norm_le γ Rw φ R hR0 α θ0 hθ0 w i
  have hstep : ptd γ Rw φ R α θ0 w (i + 1) = projBall R (ptd γ Rw φ R α θ0 w i +
      α i • tdDir γ Rw φ (ptd γ Rw φ R α θ0 w i) (w i) (w (i + 1))) := rfl
  rw [hstep, norm_sub_rev]
  generalize ptd γ Rw φ R α θ0 w i = θ at hbd ⊢
  generalize hg : tdDir γ Rw φ θ (w i) (w (i + 1)) = g
  have hne := ftd_projBall_nonexp R θ (θ + α i • g) hbd
  have hgn : ‖g‖ ≤ rmax + 2 * R := by
    rw [← hg]
    exact (ftd_tdDir_norm_le Rw rmax γ φ hRw hγ0 hγ1 hφ θ (w i) (w (i + 1))).trans
      (by linarith)
  calc ‖θ - projBall R (θ + α i • g)‖ ≤ ‖θ - (θ + α i • g)‖ := hne
    _ = α i * ‖g‖ := by
        rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ α i * (rmax + 2 * R) := mul_le_mul_of_nonneg_left hgn hα

theorem ftd_ptd_dist {S : Type} {d : ℕ} (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR0 : 0 ≤ R) (α : ℕ → ℝ)
    (θ0 : EuclideanSpace ℝ (Fin d)) (hθ0 : ‖θ0‖ ≤ R)
    (hRw : ∀ s s', |Rw s s'| ≤ rmax) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (w : ℕ → S) (a b : ℕ) (hab : a ≤ b) (hα : ∀ i, i < b → 0 ≤ α i) :
    ‖ptd γ Rw φ R α θ0 w b - ptd γ Rw φ R α θ0 w a‖ ≤
      (rmax + 2 * R) * ∑ i ∈ Finset.Ico a b, α i := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have hs := ftd_ptd_step Rw rmax γ φ R hR0 α θ0 hθ0 hRw hγ0 hγ1 hφ w n (hα n (by omega))
    have ih := ih (fun i hi => hα i (by omega))
    calc ‖ptd γ Rw φ R α θ0 w (n + 1) - ptd γ Rw φ R α θ0 w a‖
        = ‖(ptd γ Rw φ R α θ0 w (n + 1) - ptd γ Rw φ R α θ0 w n) +
            (ptd γ Rw φ R α θ0 w n - ptd γ Rw φ R α θ0 w a)‖ := by congr 1; abel
      _ ≤ ‖ptd γ Rw φ R α θ0 w (n + 1) - ptd γ Rw φ R α θ0 w n‖ +
            ‖ptd γ Rw φ R α θ0 w n - ptd γ Rw φ R α θ0 w a‖ := norm_add_le _ _
      _ ≤ α n * (rmax + 2 * R) + (rmax + 2 * R) * ∑ i ∈ Finset.Ico a n, α i := add_le_add hs ih
      _ = (rmax + 2 * R) * (∑ i ∈ Finset.Ico a n, α i + α n) := by ring

theorem ftd_zeta_mean {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (θ : EuclideanSpace ℝ (Fin d)) :
    ∑ s, ∑ s', π s * P s s' * zeta π P γ Rw φ θstar θ s s' = 0 := by
  have hz : ∀ s s', zeta π P γ Rw φ θstar θ s s' =
      ⟪tdDir γ Rw φ θ s s', θ - θstar⟫_ℝ - ⟪gbar π P γ Rw φ θ, θ - θstar⟫_ℝ := fun s s' => by
    unfold zeta; rw [inner_sub_left]
  have h1 : ∑ s, ∑ s', π s * P s s' * ⟪tdDir γ Rw φ θ s s', θ - θstar⟫_ℝ =
      ⟪gbar π P γ Rw φ θ, θ - θstar⟫_ℝ := by
    unfold gbar
    rw [sum_inner]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sum_inner]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [real_inner_smul_left]
  have h2 : ∑ s, ∑ s', π s * P s s' * ⟪gbar π P γ Rw φ θ, θ - θstar⟫_ℝ =
      ⟪gbar π P γ Rw φ θ, θ - θstar⟫_ℝ := by
    have := (ftd_stat_sum P π hP hπ (fun _ => ⟪gbar π P γ Rw φ θ, θ - θstar⟫_ℝ)).1
    rw [this, ← Finset.sum_mul, hπ.2.1, one_mul]
  simp only [hz, mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]
  ring

theorem ftd_stat_avg {S : Type} [Fintype S] [DecidableEq S] (P : S → S → ℝ) (π : S → ℝ)
    (hπ : IsStationaryDist P π) (n : ℕ) (g : S → ℝ) :
    ∑ a, π a * ∑ u, (Matrix.of P ^ n) a u * g u = ∑ u, π u * g u := by
  calc ∑ a, π a * ∑ u, (Matrix.of P ^ n) a u * g u
      = ∑ u, (∑ a, π a * (Matrix.of P ^ n) a u) * g u := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ u, π u * g u := by simp only [ftd_pow_stat P π hπ n]

theorem ftd_window {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ)
    (hP : IsStochastic P) (k n T : ℕ) (hT : k + n + 1 ≤ T)
    (Φ : (Fin (k + 1) → S) → S → S → ℝ) :
    pathExp π P T (fun w => Φ (ftd_pfx k T (by omega) w) (extendPath w (k + n))
        (extendPath w (k + n + 1))) =
      pathExp π P k (fun p => ∑ u, ∑ u', (Matrix.of P ^ n) (p (Fin.last k)) u * P u u' *
        Φ p u u') := by
  obtain ⟨j, rfl⟩ : ∃ j, T = k + n + 1 + j := ⟨T - (k + n + 1), by omega⟩
  rw [← ftd_W π P k n Φ, ← ftd_marg π P hP (k + n + 1) j]
  congr 1
  funext w
  rw [ftd_ext_apply w (k + n) (by omega), ftd_ext_apply w (k + n + 1) (by omega)]
  rfl

theorem ftd_mix_bound {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (m ρ R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1) (hR : ‖θstar‖ ≤ R)
    (hA1 : Assumption1 P π m ρ) (τ : ℕ) (ε : ℝ) (hε : m * ρ ^ τ ≤ ε)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ ≤ R) (a : S) :
    ∑ u, ∑ u', (Matrix.of P ^ τ) a u * P u u' * zeta π P γ Rw φ θstar θ u u' ≤
      4 * (rmax + 2 * R) ^ 2 * ε := by
  have hζ : ∀ u u', |zeta π P γ Rw φ θstar θ u u'| ≤ 2 * (rmax + 2 * R) ^ 2 := fun u u' =>
    (ftd_lemma10 P π Rw rmax γ φ R θstar hP hπ hRw hγ0 hγ1 hφ hR u u' θ θ hθ hθ).1
  set h : S → ℝ := fun u => ∑ u', P u u' * zeta π P γ Rw φ θstar θ u u' with hh
  have hhb : ∀ u, |h u| ≤ 2 * (rmax + 2 * R) ^ 2 := by
    intro u
    calc |h u| ≤ ∑ u', |P u u' * zeta π P γ Rw φ θstar θ u u'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u', P u u' * (2 * (rmax + 2 * R) ^ 2) := by
          refine Finset.sum_le_sum fun u' _ => ?_
          rw [abs_mul, abs_of_nonneg (hP.1 u u')]
          exact mul_le_mul_of_nonneg_left (hζ u u') (hP.1 u u')
      _ = 2 * (rmax + 2 * R) ^ 2 := by rw [← Finset.sum_mul, hP.2 u, one_mul]
  have hπh : ∑ u, π u * h u = 0 := by
    rw [← ftd_zeta_mean P π Rw γ φ θstar hP hπ θ]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hh]
    simp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u' _ => by ring
  have hτ : ∑ u, |(Matrix.of P ^ τ) a u - π u| ≤ 2 * (m * ρ ^ τ) := by
    have h := hA1.2.2.2 τ a
    unfold tvDist at h
    linarith
  have hG2 : 0 ≤ (rmax + 2 * R) ^ 2 := sq_nonneg _
  calc ∑ u, ∑ u', (Matrix.of P ^ τ) a u * P u u' * zeta π P γ Rw φ θstar θ u u'
      = ∑ u, (Matrix.of P ^ τ) a u * h u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hh]
        simp only
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u' _ => by ring
    _ = ∑ u, ((Matrix.of P ^ τ) a u - π u) * h u := by
        have : ∑ u, ((Matrix.of P ^ τ) a u - π u) * h u =
            ∑ u, (Matrix.of P ^ τ) a u * h u - ∑ u, π u * h u := by
          simp only [sub_mul, Finset.sum_sub_distrib]
        rw [this, hπh, sub_zero]
    _ ≤ ∑ u, |(Matrix.of P ^ τ) a u - π u| * (2 * (rmax + 2 * R) ^ 2) := by
        refine Finset.sum_le_sum fun u _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hhb u) (abs_nonneg _)
    _ = (∑ u, |(Matrix.of P ^ τ) a u - π u|) * (2 * (rmax + 2 * R) ^ 2) := by rw [Finset.sum_mul]
    _ ≤ 2 * (m * ρ ^ τ) * (2 * (rmax + 2 * R) ^ 2) :=
        mul_le_mul_of_nonneg_right hτ (by positivity)
    _ ≤ 4 * (rmax + 2 * R) ^ 2 * ε := by
        nlinarith [mul_nonneg hG2 (sub_nonneg.mpr hε)]

theorem ftd_lemma11 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hA1 : Assumption1 P π m ρ)
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    ∀ (T : ℕ) (α : ℕ → ℝ), (∀ i j, i ≤ j → j ≤ T → α j ≤ α i) → 0 < α T →
      ∀ t < T,
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ (rmax + 2 * R) ^ 2 * (4 + 6 * (tauMix m ρ (α T) : ℝ)) * α (t - tauMix m ρ (α T)) ∧
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * (rmax + 2 * R) ^ 2 * ∑ i ∈ Finset.range t, α i := by
  intro T α hmono hαT t ht
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  obtain ⟨s0⟩ : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hπ.2.1
    simp at this
  have hrmax : 0 ≤ rmax := (abs_nonneg _).trans (hRw s0 s0)
  have hGn : 0 ≤ rmax + 2 * R := by linarith
  have hX : 0 ≤ (rmax + 2 * R) ^ 2 := sq_nonneg _
  have hαpos : ∀ i, i ≤ T → 0 < α i := fun i hi => lt_of_lt_of_le hαT (hmono i T hi le_rfl)
  have hm := hA1.1
  have hρ1 := hA1.2.2.1
  have hτex : ∃ n : ℕ, m * ρ ^ n ≤ α T := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hαT hm) hρ1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hm] at hn
    linarith
  have hτ : m * ρ ^ (tauMix m ρ (α T)) ≤ α T := by
    unfold tauMix
    exact Nat.sInf_mem hτex
  generalize tauMix m ρ (α T) = τ at hτ ⊢
  have hnorm : ∀ (w : Fin (T + 1) → S) (a : ℕ), ‖ptd γ Rw φ R α θ0 (extendPath w) a‖ ≤ R :=
    fun w a => ftd_ptd_norm_le γ Rw φ R hR0 α θ0 hθ0 _ a
  -- pointwise Lipschitz comparison with an earlier iterate
  have hZ : ∀ (w : Fin (T + 1) → S) (a : ℕ), a ≤ t →
      zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t) (extendPath w t)
          (extendPath w (t + 1)) ≤
        zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) a) (extendPath w t)
          (extendPath w (t + 1)) +
        6 * (rmax + 2 * R) * ((rmax + 2 * R) * ∑ i ∈ Finset.Ico a t, α i) := by
    intro w a hat
    have h1 := ftd_ptd_dist Rw rmax γ φ R hR0 α θ0 hθ0 hRw hγ0 hγ1 hφ (extendPath w) a t hat
      (fun i hi => (hαpos i (by omega)).le)
    have h2 := (ftd_lemma10 P π Rw rmax γ φ R θstar hP hπ hRw hγ0 hγ1 hφ hR (extendPath w t)
      (extendPath w (t + 1)) _ _ (hnorm w t) (hnorm w a)).2
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 6 * (rmax + 2 * R))
    have h4 := le_abs_self (zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
          (extendPath w t) (extendPath w (t + 1)) -
        zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) a) (extendPath w t)
          (extendPath w (t + 1)))
    nlinarith
  -- second bound
  have hE0 : pathExp π P T (fun w => zeta π P γ Rw φ θstar θ0 (extendPath w t)
      (extendPath w (t + 1))) = 0 := by
    have := ftd_window π P hP 0 t T (by omega)
      (fun _ u u' => zeta π P γ Rw φ θstar θ0 u u')
    simp only [Nat.zero_add] at this
    rw [this, ftd_pathExp_zero]
    have e : ∀ a : S, (∑ u, ∑ u', (Matrix.of P ^ t) a u * P u u' *
        zeta π P γ Rw φ θstar θ0 u u') =
        ∑ u, (Matrix.of P ^ t) a u * (∑ u', P u u' * zeta π P γ Rw φ θstar θ0 u u') := by
      intro a
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u' _ => by ring
    simp only [e]
    rw [ftd_stat_avg P π hπ t (fun u => ∑ u', P u u' * zeta π P γ Rw φ θstar θ0 u u')]
    rw [← ftd_zeta_mean P π Rw γ φ θstar hP hπ θ0]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u' _ => by ring
  have hB2 : pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
      (extendPath w t) (extendPath w (t + 1))) ≤
      6 * (rmax + 2 * R) ^ 2 * ∑ i ∈ Finset.range t, α i := by
    have hm1 := ftd_pathExp_mono π P hP hπ T _
      (fun w => zeta π P γ Rw φ θstar θ0 (extendPath w t) (extendPath w (t + 1)) +
        6 * (rmax + 2 * R) * ((rmax + 2 * R) * ∑ i ∈ Finset.Ico 0 t, α i))
      (fun w => hZ w 0 (Nat.zero_le _))
    rw [ftd_pathExp_add, hE0, ftd_pathExp_const π P hP hπ] at hm1
    rw [Finset.range_eq_Ico]
    refine hm1.trans (le_of_eq ?_)
    ring
  refine ⟨?_, hB2⟩
  rcases lt_or_ge t τ with htτ | hτt
  · -- t < τ : use the second bound
    rw [Nat.sub_eq_zero_of_le htτ.le]
    have hsum : ∑ i ∈ Finset.range t, α i ≤ t * α 0 := by
      have := Finset.sum_le_card_nsmul (Finset.range t) α (α 0)
        (fun i hi => hmono 0 i (Nat.zero_le _) (by have := Finset.mem_range.mp hi; omega))
      simpa using this
    have ha0 := hαpos 0 (Nat.zero_le _)
    have htτ' : (t : ℝ) ≤ τ := Nat.cast_le.mpr htτ.le
    have h6 : 0 ≤ (rmax + 2 * R) ^ 2 * α 0 := mul_nonneg hX ha0.le
    nlinarith [mul_nonneg h6 (sub_nonneg.mpr htτ'), mul_le_mul_of_nonneg_left hsum hX]
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + τ := ⟨t - τ, by omega⟩
    rw [Nat.add_sub_cancel]
    have hsum : ∑ i ∈ Finset.Ico t' (t' + τ), α i ≤ τ * α t' := by
      have := Finset.sum_le_card_nsmul (Finset.Ico t' (t' + τ)) α (α t')
        (fun i hi => hmono t' i (Finset.mem_Ico.mp hi).1
          (by have := (Finset.mem_Ico.mp hi).2; omega))
      simpa using this
    have hαT' : α T ≤ α t' := hmono t' T (by omega) le_rfl
    -- decoupling estimate
    have hE : pathExp π P T (fun w => zeta π P γ Rw φ θstar
        (ptd γ Rw φ R α θ0 (extendPath w) t') (extendPath w (t' + τ))
        (extendPath w (t' + τ + 1))) ≤ 4 * (rmax + 2 * R) ^ 2 * α T := by
      have hw := ftd_window π P hP t' τ T (by omega)
        (fun p u u' => zeta π P γ Rw φ θstar
          (ptd γ Rw φ R α θ0 (extendPath p) t') u u')
      have hc : (fun w : Fin (T + 1) → S => zeta π P γ Rw φ θstar
          (ptd γ Rw φ R α θ0 (extendPath (ftd_pfx t' T (by omega) w)) t')
          (extendPath w (t' + τ)) (extendPath w (t' + τ + 1))) =
          fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t')
            (extendPath w (t' + τ)) (extendPath w (t' + τ + 1)) := by
        funext w
        rw [ftd_ptd_congr γ Rw φ R α θ0 (extendPath (ftd_pfx t' T (by omega) w)) (extendPath w) t'
          (fun i hi => by
            rw [ftd_ext_apply (ftd_pfx t' T (by omega) w) i hi, ftd_ext_apply w i (by omega)]
            rfl)]
      rw [hc] at hw
      rw [hw]
      calc pathExp π P t' (fun p => ∑ u, ∑ u', (Matrix.of P ^ τ) (p (Fin.last t')) u * P u u' *
            zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath p) t') u u')
          ≤ pathExp π P t' (fun _ => 4 * (rmax + 2 * R) ^ 2 * α T) :=
            ftd_pathExp_mono π P hP hπ t' _ _ (fun p =>
              ftd_mix_bound P π Rw rmax γ φ m ρ R θstar hP hπ hRw hγ0 hγ1 hφ hR hA1 τ (α T) hτ
                _ (ftd_ptd_norm_le γ Rw φ R hR0 α θ0 hθ0 _ t') _)
        _ = 4 * (rmax + 2 * R) ^ 2 * α T := ftd_pathExp_const π P hP hπ t' _
    have hm1 := ftd_pathExp_mono π P hP hπ T _
      (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t')
          (extendPath w (t' + τ)) (extendPath w (t' + τ + 1)) +
        6 * (rmax + 2 * R) * ((rmax + 2 * R) * ∑ i ∈ Finset.Ico t' (t' + τ), α i))
      (fun w => hZ w t' (by omega))
    rw [ftd_pathExp_add, ftd_pathExp_const π P hP hπ] at hm1
    have hα0 : 0 ≤ α t' := (hαpos t' (by omega)).le
    have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg hX (by norm_num : (0:ℝ) ≤ 6)),
      mul_le_mul_of_nonneg_left hαT' (mul_nonneg hX (by norm_num : (0:ℝ) ≤ 4))]

theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hA1 : Assumption1 P π m ρ)
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    ∀ (T : ℕ) (α : ℕ → ℝ), (∀ i j, i ≤ j → j ≤ T → α j ≤ α i) → 0 < α T →
      ∀ t < T,
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ (rmax + 2 * R) ^ 2 * (4 + 6 * (tauMix m ρ (α T) : ℝ)) * α (t - tauMix m ρ (α T)) ∧
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * (rmax + 2 * R) ^ 2 * ∑ i ∈ Finset.range t, α i :=
  ftd_lemma11 P π Rw rmax γ φ m ρ R θstar θ0 hP hπ hRw hγ0 hγ1 hφ hstar hA1 hR hθ0
