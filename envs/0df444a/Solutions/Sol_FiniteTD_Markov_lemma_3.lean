-- Prove2me | solution 1 for FiniteTD.Markov.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:16:34.044478+00:00
-- url     : https://prove2.me/submissions/b4c6a32a-1fab-45a6-9189-08cad628e09a

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

set_option autoImplicit false
open FiniteTD.Markov
open scoped InnerProductSpace

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

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - γ) * dNormSq π φ (θstar - θ) ≤ ⟪θstar - θ, gbar π P γ Rw φ θ⟫_ℝ :=
  ftd_lemma3 P π Rw γ φ θstar hP hπ hγ0 hγ1 hstar
