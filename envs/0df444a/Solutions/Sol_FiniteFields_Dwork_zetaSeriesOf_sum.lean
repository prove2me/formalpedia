-- Prove2me | solution 1 for FiniteFields.Dwork.zetaSeriesOf_sum
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:49:51.636856+00:00
-- url     : https://prove2.me/submissions/77543a11-5d7a-4393-a8b6-5e198375e523

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy
section
noncomputable section
namespace FiniteFields
open PowerSeries
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (countingSeries N) = (N n : ℚ) := by
  simp [countingSeries]
theorem IsZetaSeries.unique {N : ℕ → ℕ} {Z W : ℚ⟦X⟧}
    (hZ : IsZetaSeries N Z) (hW : IsZetaSeries N W) : Z = W := by
  exact PowerSeries.eq_of_derivative_eq_mul
    (by simpa only [mul_comm] using hZ.2) (by simpa only [mul_comm] using hW.2)
    (hZ.1.trans hW.1.symm)
end FiniteFields
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
@[simp]
theorem constantCoeff_zetaLog (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (zetaLog N) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, zetaLog, PowerSeries.coeff_mk]
  simp
theorem derivative_zetaLog (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (zetaLog N) = countingSeries N := by
  ext n
  rw [PowerSeries.coeff_derivative, zetaLog, PowerSeries.coeff_mk, coeff_countingSeries]
  have hne : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring
theorem constantCoeff_zetaSeriesOf (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (zetaSeriesOf N) = 1 := by
  rw [zetaSeriesOf, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_zetaLog N)), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_zetaLog]
theorem derivative_zetaSeriesOf (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (zetaSeriesOf N) = countingSeries N * zetaSeriesOf N := by
  rw [zetaSeriesOf, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_zetaLog N)),
    PowerSeries.derivative_exp, derivative_zetaLog, mul_comm]
theorem zetaSeriesOf_isZetaSeries (N : ℕ → ℕ) : IsZetaSeries N (zetaSeriesOf N) :=
  ⟨constantCoeff_zetaSeriesOf N, derivative_zetaSeriesOf N⟩
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section ZetaCalculus
theorem countingSeries_add (N₁ N₂ : ℕ → ℕ) :
    countingSeries (fun n ↦ N₁ n + N₂ n) = countingSeries N₁ + countingSeries N₂ := by
  ext n
  rw [map_add, coeff_countingSeries, coeff_countingSeries, coeff_countingSeries, Nat.cast_add]
theorem zetaSeriesOf_add (N₁ N₂ : ℕ → ℕ) :
    zetaSeriesOf (fun n ↦ N₁ n + N₂ n) = zetaSeriesOf N₁ * zetaSeriesOf N₂ := by
  refine (zetaSeriesOf_isZetaSeries _).unique ⟨?_, ?_⟩
  · rw [map_mul, constantCoeff_zetaSeriesOf, constantCoeff_zetaSeriesOf, one_mul]
  · rw [(PowerSeries.derivative ℚ).leibniz, smul_eq_mul, smul_eq_mul,
      derivative_zetaSeriesOf, derivative_zetaSeriesOf, countingSeries_add]
    ring
theorem zetaSeriesOf_zero_counts : zetaSeriesOf (fun _ ↦ 0) = 1 := by
  refine (zetaSeriesOf_isZetaSeries _).unique ⟨by rw [map_one], ?_⟩
  have h0 : countingSeries (fun _ : ℕ ↦ 0) = 0 := by
    ext n
    rw [coeff_countingSeries, map_zero, Nat.cast_zero]
  rw [h0, zero_mul]
  exact Derivation.map_one_eq_zero _
end ZetaCalculus
end FiniteFields.Dwork
end
end
open PowerSeries
open FiniteFields.Dwork
theorem solution {ι : Type*} (s : Finset ι) (N : ι → ℕ → ℕ) :
    zetaSeriesOf (fun n ↦ ∑ i ∈ s, N i n) = ∏ i ∈ s, zetaSeriesOf (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zetaSeriesOf_zero_counts
  | @insert i s hi ih =>
      have hfun : (fun n ↦ ∑ j ∈ insert i s, N j n)
          = fun n ↦ N i n + ∑ j ∈ s, N j n := by
        funext n
        rw [Finset.sum_insert hi]
      rw [hfun, zetaSeriesOf_add, Finset.prod_insert hi, ih]
