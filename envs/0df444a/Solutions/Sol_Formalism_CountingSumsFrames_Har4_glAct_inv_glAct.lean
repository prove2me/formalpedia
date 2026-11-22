-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_inv_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:23.488384+00:00
-- url     : https://prove2.me/submissions/1a1a3e39-ff8b-46c0-9e04-c2383e38b75e

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (f : PolXY K k) :
    glAct g⁻¹ (glAct g f) = f := by
  have key : (glAct g⁻¹).comp (glAct g) = AlgHom.id K (PolXY K k) := by
    apply MvPolynomial.algHom_ext
    rintro (i | i)
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, glAct_X_inl, map_sum, map_mul,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
      have hm : ∀ l : Fin k, C (∑ j : Fin k, (g : Matrix (Fin k) (Fin k) K) i j *
          ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) = (if i = l then 1 else 0 : PolXY K k) := by
        intro l
        rw [← Matrix.mul_apply, Units.mul_inv, Matrix.one_apply]
        split_ifs <;> simp
      calc ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) *
            ∑ l : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) * X (Sum.inl l)
          = ∑ l : Fin k, C (∑ j : Fin k, (g : Matrix (Fin k) (Fin k) K) i j *
              ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) * X (Sum.inl l) := by
            simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc, Finset.mul_sum]
            rw [Finset.sum_comm]
        _ = X (Sum.inl i) := by
          simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, glAct_X_inr, map_sum, map_mul,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, inv_inv]
      have hm : ∀ l : Fin k, C (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
          (g : Matrix (Fin k) (Fin k) K) l j) = (if i = l then 1 else 0 : PolXY K k) := by
        intro l
        have e : (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
            (g : Matrix (Fin k) (Fin k) K) l j) = ((g : Matrix (Fin k) (Fin k) K) *
            ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) l i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        rw [e, Units.mul_inv, Matrix.one_apply]
        by_cases h : i = l
        · subst h; simp
        · simp [h, Ne.symm h]
      calc ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) *
            ∑ l : Fin k, C ((g : Matrix (Fin k) (Fin k) K) l j) * X (Sum.inr l)
          = ∑ l : Fin k, C (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
              (g : Matrix (Fin k) (Fin k) K) l j) * X (Sum.inr l) := by
            simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc, Finset.mul_sum]
            rw [Finset.sum_comm]
        _ = X (Sum.inr i) := by
          simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 := congrArg (fun φ => φ f) key
  simpa using h2
end Formalism.CountingSumsFrames.Har4
