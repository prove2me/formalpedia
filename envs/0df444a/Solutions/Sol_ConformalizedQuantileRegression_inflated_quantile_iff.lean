-- Prove2me | solution 1 for ConformalizedQuantileRegression.inflated_quantile_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:02:26.701986+00:00
-- url     : https://prove2.me/submissions/eb112443-6a76-425f-852f-2fbd78bf5251

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory
namespace ConformalizedQuantileRegression

theorem inflated_quantile_iff {n : ℕ} (hn : 0 < n) (z : Fin (n + 1) → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (z (Fin.last n) : EReal) ≤ empQuantile (Finset.univ.map Fin.castSuccEmb) z ((1 + 1 / (n : ℝ)) * α) ↔
      (z (Fin.last n) : EReal) ≤ empQuantile Finset.univ z α := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have key : ∀ y : ℝ, y < z (Fin.last n) →
      ((1 + 1 / (n : ℝ)) * α ≤ empCDF (Finset.univ.map Fin.castSuccEmb) z y ↔
        α ≤ empCDF Finset.univ z y) := by
    intro y hy
    have h1 : (Finset.univ.filter fun i => z i ≤ y).card =
        ((Finset.univ.map Fin.castSuccEmb).filter fun i => z i ≤ y).card := by
      rw [Fin.univ_castSuccEmb, Finset.filter_cons, if_neg (not_le.mpr hy)]
    simp only [empCDF, h1, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    set c : ℝ := (((Finset.univ.map Fin.castSuccEmb).filter fun i => z i ≤ y).card : ℝ)
    have e : (1 + 1 / (n:ℝ)) * α * n = α * (n + 1) := by field_simp
    push_cast
    rw [le_div_iff₀ hnpos, e, le_div_iff₀ (by positivity)]
  simp only [empQuantile, le_iInf₂_iff]
  constructor
  · intro h y hy
    by_contra hlt
    have hlt' : y < z (Fin.last n) := by exact_mod_cast not_le.mp hlt
    exact hlt (h y ((key y hlt').2 hy))
  · intro h y hy
    by_contra hlt
    have hlt' : y < z (Fin.last n) := by exact_mod_cast not_le.mp hlt
    exact hlt (h y ((key y hlt').1 hy))

end ConformalizedQuantileRegression

open ConformalizedQuantileRegression in
theorem solution {n : ℕ} (hn : 0 < n) (z : Fin (n + 1) → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (z (Fin.last n) : EReal) ≤ empQuantile (Finset.univ.map Fin.castSuccEmb) z ((1 + 1 / (n : ℝ)) * α) ↔
      (z (Fin.last n) : EReal) ≤ empQuantile Finset.univ z α :=
  ConformalizedQuantileRegression.inflated_quantile_iff hn z α hα0 hα1
