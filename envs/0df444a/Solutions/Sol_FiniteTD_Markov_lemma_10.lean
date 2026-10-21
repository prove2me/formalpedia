-- Prove2me | solution 1 for FiniteTD.Markov.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:19:02.878564+00:00
-- url     : https://prove2.me/submissions/1a8b921a-5b90-4bd2-9db4-8eb2c5b92c1f

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

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) :
    ∀ (s s' : S) (θ θ' : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ‖θ'‖ ≤ R →
      |zeta π P γ Rw φ θstar θ s s'| ≤ 2 * (rmax + 2 * R) ^ 2 ∧
      |zeta π P γ Rw φ θstar θ s s' - zeta π P γ Rw φ θstar θ' s s'|
        ≤ 6 * (rmax + 2 * R) * ‖θ - θ'‖ :=
  ftd_lemma10 P π Rw rmax γ φ R θstar hP hπ hRw hγ0 hγ1 hφ hR
