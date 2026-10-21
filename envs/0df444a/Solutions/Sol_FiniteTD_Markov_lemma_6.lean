-- Prove2me | solution 1 for FiniteTD.Markov.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:10:17.393402+00:00
-- url     : https://prove2.me/submissions/dd8ddff4-667d-4d0f-bbb9-841768e225d9

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
theorem solution {S : Type} [Fintype S] {d : ℕ}
    (Rw : S → S → ℝ) (rmax γ : ℝ) (φ : S → EuclideanSpace ℝ (Fin d))
    (hRw : ∀ s s', |Rw s s'| ≤ rmax) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1) :
    ∀ (θ : EuclideanSpace ℝ (Fin d)) (s s' : S),
      ‖tdDir γ Rw φ θ s s'‖ ≤ rmax + 2 * ‖θ‖ :=
  fun θ s s' => ftd_tdDir_norm_le Rw rmax γ φ hRw hγ0 hγ1 hφ θ s s'
