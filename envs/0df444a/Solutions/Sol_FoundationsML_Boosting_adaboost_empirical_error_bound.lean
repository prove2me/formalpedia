-- Prove2me | solution 1 for FoundationsML.Boosting.adaboost_empirical_error_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:22:44.086255+00:00
-- url     : https://prove2.me/submissions/137e67d6-f6f0-4e92-bdf1-9bc420f4f7a9

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalError
import Definitions.Def_FoundationsML_Boosting_AdaBoostEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- Two-point sample on `Unit` with opposite labels. -/
noncomputable def aux_abeb_y : Fin 2 → ℝ := ![1, -1]

/-- The constant base classifier `+1`. -/
noncomputable def aux_abeb_h : ℕ → Unit → ℝ := fun _ _ => 1

theorem aux_abeb_eps0 :
    AdaBoostEpsilon (fun _ : Fin 2 => ()) aux_abeb_y aux_abeb_h 0 = 1 / 2 := by
  simp only [AdaBoostEpsilon, WeightedError, AdaBoostDist, aux_abeb_y, aux_abeb_h,
    Fin.sum_univ_two]
  norm_num

theorem aux_abeb_err :
    EmpiricalError (fun _ : Fin 2 => ()) aux_abeb_y
      (AdaBoostEnsemble (fun _ : Fin 2 => ()) aux_abeb_y aux_abeb_h 1) = 1 := by
  have hα : AdaBoostAlpha (AdaBoostEpsilon (fun _ : Fin 2 => ()) aux_abeb_y aux_abeb_h 0)
      = 0 := by
    rw [aux_abeb_eps0, AdaBoostAlpha]
    norm_num
  simp only [EmpiricalError, AdaBoostEnsemble, Finset.sum_range_one, hα, zero_mul, mul_zero,
    le_refl, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

end FoundationsML.Boosting

open FoundationsML.Boosting

theorem solution : ¬ (∀ {X : Type} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1),
    EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) ∧
      (∀ γ : ℝ, (∀ t < T, γ ≤ 1 / 2 - AdaBoostEpsilon S y h t) →
        EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
          Real.exp (-2 * γ ^ 2 * T))) := by
  intro H
  have hy : ∀ i, aux_abeb_y i = 1 ∨ aux_abeb_y i = -1 := by
    intro i
    fin_cases i <;> simp [aux_abeb_y]
  have hh : ∀ t < 1, ∀ x, aux_abeb_h t x = 1 ∨ aux_abeb_h t x = -1 := by
    intro t _ x
    left; rfl
  have hne : ∀ t < 1, AdaBoostEpsilon (fun _ : Fin 2 => ()) aux_abeb_y aux_abeb_h t ≠ 0 ∧
      AdaBoostEpsilon (fun _ : Fin 2 => ()) aux_abeb_y aux_abeb_h t ≠ 1 := by
    intro t ht
    have : t = 0 := by omega
    subst this
    rw [aux_abeb_eps0]
    norm_num
  have H2 := (H (X := Unit) (m := 2) (by norm_num) (fun _ => ()) aux_abeb_y hy 1 aux_abeb_h
    hh hne).2 (-1) (by
      intro t ht
      have : t = 0 := by omega
      subst this
      rw [aux_abeb_eps0]
      norm_num)
  rw [aux_abeb_err] at H2
  have hlt : Real.exp (-2 * (-1 : ℝ) ^ 2 * ((1 : ℕ) : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith
