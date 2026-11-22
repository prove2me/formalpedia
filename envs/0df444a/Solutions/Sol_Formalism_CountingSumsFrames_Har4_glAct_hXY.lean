-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_hXY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:49.625292+00:00
-- url     : https://prove2.me/submissions/02fd9192-24c4-4976-9f28-7850be0c1812

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_X_inl
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_X_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by
  have hm : ∀ j l : Fin k, C (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) =
      (if l = j then 1 else 0 : PolXY K k) := by
    intro j l
    have e : (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) = (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) * (g : Matrix (Fin k) (Fin k) K)) l j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs <;> simp
  unfold hXY
  simp only [map_sum, map_mul, glAct_X_inl, glAct_X_inr]
  calc ∑ i : Fin k, (∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
        (∑ l : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l))
      = ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k, (C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
          (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) := by
        simp only [Finset.sum_mul_sum]
    _ = ∑ j : Fin k, ∑ l : Fin k, ∑ i : Fin k, (C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
          (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_comm)
    _ = ∑ j : Fin k, ∑ l : Fin k, C (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) *
          (X (Sum.inl j) * X (Sum.inr l)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    _ = ∑ i : Fin k, X (Sum.inl i) * X (Sum.inr i) := by
        simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
end Formalism.CountingSumsFrames.Har4
