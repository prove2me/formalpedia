-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_det_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.6757+00:00
-- url     : https://prove2.me/submissions/78b00d70-eae2-4ca9-97e0-137ccd784181

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_mul_eq_sum_prod_mul_det_submatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_injective_fin_le_factorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ)
    (ρ Q : ℝ) (hρ : 1 ≤ ρ) (hQ : 0 ≤ Q) (hX : ∀ i k, ‖X i k‖ ≤ ρ)
    (hY : ∀ f : Fin t → Fin N, ‖(Y.submatrix f id).det‖ ≤ Q) :
    ‖(X * Y).det‖ ≤ (N.factorial : ℝ) * ρ ^ N * Q := by
  classical
  rw [det_mul_eq_sum_prod_mul_det_submatrix]
  have hterm : ∀ f : Fin t → Fin N, ‖(∏ i, X i (f i)) * (Y.submatrix f id).det‖ ≤
      if Function.Injective f then ρ ^ N * Q else 0 := by
    intro f
    split_ifs with hf
    · have htN : t ≤ N := by simpa using Fintype.card_le_of_injective f hf
      rw [norm_mul, norm_prod]
      apply mul_le_mul _ (hY f) (norm_nonneg _) (by positivity)
      calc ∏ i, ‖X i (f i)‖ ≤ ∏ _i : Fin t, ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hX _ _)
        _ = ρ ^ t := by simp
        _ ≤ ρ ^ N := pow_le_pow_right₀ hρ htN
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
        simpa [Function.Injective] using hf
      rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])]; simp
  calc _ ≤ ∑ f : Fin t → Fin N, ‖(∏ i, X i (f i)) * (Y.submatrix f id).det‖ := norm_sum_le _ _
    _ ≤ ∑ f : Fin t → Fin N, if Function.Injective f then ρ ^ N * Q else 0 :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = ((Finset.univ.filter (fun f : Fin t → Fin N => Function.Injective f)).card : ℝ) *
        (ρ ^ N * Q) := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N.factorial : ℝ) * (ρ ^ N * Q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_injective_fin_le_factorial t N
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
