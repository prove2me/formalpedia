-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:03:36.829279+00:00
-- url     : https://prove2.me/submissions/d617bef4-6791-442a-829e-7d047c5f24e8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_choose_mul_norm_blockAverage_408915f

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **BKL Lemma 2.2** (orthogonal-representation form): `‖v‖ ≤ 4^d ‖S_Q v‖`. -/
theorem solution (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ (4 : ℝ) ^ d * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ := by
    have hchoose_nat : (2 * d).choose d ≤ 4 ^ d := by
      simpa only [Nat.centralBinom_eq_two_mul_choose] using
        (Nat.centralBinom_le_four_pow d)
    have hchoose_real : ((2 * d).choose d : ℝ) ≤ (4 : ℝ) ^ d := by
      exact_mod_cast hchoose_nat
    have hnorm : 0 ≤ ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ := norm_nonneg _
    calc
      ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ :=
        FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_408915f ρ hA hB hAB hAQ hQ hQc v hvA hvB
      _ ≤ (4 : ℝ) ^ d * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ :=
        mul_le_mul_of_nonneg_right hchoose_real hnorm
