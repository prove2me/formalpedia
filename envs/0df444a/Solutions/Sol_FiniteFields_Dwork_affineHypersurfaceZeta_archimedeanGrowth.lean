-- Prove2me | solution 1 for FiniteFields.Dwork.affineHypersurfaceZeta_archimedeanGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:31:00.419627+00:00
-- url     : https://prove2.me/submissions/ecb17b4f-e325-4cb9-bc71-4b25b29f9c9f

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Foundations
section
noncomputable section
namespace FiniteFields
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem natCard_extension (n : ℕ) :
    Nat.card (Extension k p n) = Nat.card k ^ (n + 1) := by
  exact FiniteField.natCard_extension k p (n + 1)
theorem natCard_affinePoints (d n : ℕ) :
    Nat.card (AffinePoints k p d n) =
      (Nat.card k ^ (n + 1)) ^ d := by
  rw [Nat.card_fun, Nat.card_fin, natCard_extension]
end FiniteFields
end
end
section
noncomputable section
namespace FiniteFields
open PowerSeries
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (countingSeries N) = (N n : ℚ) := by
  simp [countingSeries]
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
theorem affineHypersurfacePointCount_eq_tupleCount (f : MvPolynomial (Fin d) k) (n : ℕ) :
    affineHypersurfacePointCount k p f n = Nat.card (AffineHypersurfaceTuples k p f n) :=
  Nat.card_congr (affineHypersurfaceExtensionPointEquiv k p f n)
theorem affineHypersurfacePointCount_le (f : MvPolynomial (Fin d) k) (n : ℕ) :
    affineHypersurfacePointCount k p f n ≤ (Nat.card k ^ (n + 1)) ^ d := by
  rw [affineHypersurfacePointCount_eq_tupleCount]
  calc Nat.card (AffineHypersurfaceTuples k p f n)
      ≤ Nat.card (Fin d → Extension k p n) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = (Nat.card k ^ (n + 1)) ^ d := natCard_affinePoints k p d n
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
theorem coeff_succ_of_isZetaSeries {N : ℕ → ℕ} {Z : ℚ⟦X⟧} (hZ : IsZetaSeries N Z) (m : ℕ) :
    PowerSeries.coeff (m + 1) Z * ((m : ℚ) + 1)
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, (N ij.1 : ℚ) * PowerSeries.coeff ij.2 Z := by
  have h := congrArg (PowerSeries.coeff m) hZ.2
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_countingSeries]
theorem coeff_zetaSeriesOf_bound {N : ℕ → ℕ} {Q : ℕ} (hN : ∀ n, N n ≤ Q ^ (n + 1)) (m : ℕ) :
    0 ≤ PowerSeries.coeff m (zetaSeriesOf N) ∧
      PowerSeries.coeff m (zetaSeriesOf N) ≤ (Q : ℚ) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      cases m with
      | zero =>
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_zetaSeriesOf]
          norm_num
      | succ m =>
          have hrec := coeff_succ_of_isZetaSeries (zetaSeriesOf_isZetaSeries N) m
          have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
              0 ≤ (N ij.1 : ℚ) * PowerSeries.coeff ij.2 (zetaSeriesOf N) ∧
                (N ij.1 : ℚ) * PowerSeries.coeff ij.2 (zetaSeriesOf N) ≤ (Q : ℚ) ^ (m + 1) := by
            rintro ⟨i, j⟩ hij
            have hsum : i + j = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
            obtain ⟨hj0, hjle⟩ := ih j (by omega)
            have hNi : (N i : ℚ) ≤ (Q : ℚ) ^ (i + 1) := by exact_mod_cast hN i
            refine ⟨by positivity, ?_⟩
            calc (N i : ℚ) * PowerSeries.coeff j (zetaSeriesOf N)
                ≤ (Q : ℚ) ^ (i + 1) * (Q : ℚ) ^ j :=
                  mul_le_mul hNi hjle hj0 (by positivity)
              _ = (Q : ℚ) ^ (m + 1) := by rw [← pow_add]; congr 1; omega
          have hcard : (Finset.HasAntidiagonal.antidiagonal m).card = m + 1 := Finset.Nat.card_antidiagonal m
          have hpos : (0 : ℚ) < (m : ℚ) + 1 := by positivity
          constructor
          · have hsum0 : 0 ≤ PowerSeries.coeff (m + 1) (zetaSeriesOf N) * ((m : ℚ) + 1) := by
              rw [hrec]
              exact Finset.sum_nonneg fun ij hij => (hterm ij hij).1
            nlinarith [hsum0]
          · have hsumle : PowerSeries.coeff (m + 1) (zetaSeriesOf N) * ((m : ℚ) + 1)
                ≤ ((m : ℚ) + 1) * (Q : ℚ) ^ (m + 1) := by
              rw [hrec]
              calc ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, (N ij.1 : ℚ) * PowerSeries.coeff ij.2 (zetaSeriesOf N)
                  ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal m, (Q : ℚ) ^ (m + 1) :=
                    Finset.sum_le_sum fun ij hij => (hterm ij hij).2
                _ = ((m : ℚ) + 1) * (Q : ℚ) ^ (m + 1) := by
                    rw [Finset.sum_const, hcard, nsmul_eq_mul]
                    push_cast
                    ring
            nlinarith [hsumle]
end FiniteFields.Dwork
end
end
open FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem solution (f : MvPolynomial (Fin d) k) (m : ℕ) :
    0 ≤ PowerSeries.coeff m (affineHypersurfaceZetaSeries k p f) ∧
      PowerSeries.coeff m (affineHypersurfaceZetaSeries k p f)
        ≤ ((Nat.card k ^ d : ℕ) : ℚ) ^ m := by
  refine coeff_zetaSeriesOf_bound (fun n => ?_) m
  have h := affineHypersurfacePointCount_le k p f n
  calc affineHypersurfacePointCount k p f n
      ≤ (Nat.card k ^ (n + 1)) ^ d := h
    _ = (Nat.card k ^ d) ^ (n + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
