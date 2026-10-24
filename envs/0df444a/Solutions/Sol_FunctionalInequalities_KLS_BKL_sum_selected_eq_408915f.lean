-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sum_selected_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:16:57.697335+00:00
-- url     : https://prove2.me/submissions/4c6be601-f0b3-4c0d-93fb-5cda3f4ad2f9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
variable {n : ℕ}
section Masks
theorem FunctionalInequalities.KLS.BKL.selected_succ {E : Type*} {k : ℕ} (h : Fin (k+1) → E) (q : Fin (k+1) → Bool) :
    selected h q = if q 0 = true then h 0 :: selected (Fin.tail h) (Fin.tail q)
      else selected (Fin.tail h) (Fin.tail q) := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.selected_zero {E : Type*} (h : Fin 0 → E) (q : Fin 0 → Bool) : selected h q = [] := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.maskCount_succ {k : ℕ} (q : Fin (k+1) → Bool) :
    maskCount q = (if q 0 = true then 1 else 0) + maskCount (Fin.tail q) := by
  rw [maskCount, maskCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl
theorem FunctionalInequalities.KLS.BKL.maskCount_zero (q : Fin 0 → Bool) : maskCount q = 0 := by
  simp [maskCount]
theorem FunctionalInequalities.KLS.BKL.tail_not {k : ℕ} (q : Fin (k+1) → Bool) :
    Fin.tail (fun i => !(q i)) = fun i => !(Fin.tail q i) := rfl
theorem FunctionalInequalities.KLS.BKL.sum_cons_split {ι : Type*} [Fintype ι] {k : ℕ} (F : (Fin (k+1) → ι) → ℝ) :
    ∑ J : Fin (k+1) → ι, F J = ∑ j : ι, ∑ J' : Fin k → ι, F (Fin.cons j J') := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities.KLS.BKL in
/-- Reindex a mask-selected sum as a double sum over the selected and the complementary slots. -/
theorem solution {E ι : Type*} [Fintype ι] (w : ι → E) :
    ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
      FunctionalInequalities.KLS.BKL.maskCount q = c₁ → FunctionalInequalities.KLS.BKL.maskCount (fun i => !(q i)) = c₂ →
      ∑ J : Fin k → ι, G (FunctionalInequalities.Analysis.selected (fun i => w (J i)) q)
          (FunctionalInequalities.Analysis.selected (fun i => w (J i)) (fun i => !(q i))) =
        ∑ J₁ : Fin c₁ → ι, ∑ J₂ : Fin c₂ → ι,
          G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) := by
  intro k
  induction k with
  | zero =>
    intro q G c₁ c₂ h1 h2
    rw [FunctionalInequalities.KLS.BKL.maskCount_zero] at h1 h2
    subst h1
    subst h2
    simp [FunctionalInequalities.KLS.BKL.selected_zero, List.ofFn_zero]
  | succ k ih =>
    intro q G c₁ c₂ h1 h2
    rw [FunctionalInequalities.KLS.BKL.sum_cons_split]
    rw [FunctionalInequalities.KLS.BKL.maskCount_succ] at h1
    rw [FunctionalInequalities.KLS.BKL.maskCount_succ, FunctionalInequalities.KLS.BKL.tail_not] at h2
    have hsel : ∀ (j : ι) (J' : Fin k → ι) (p : Fin (k+1) → Bool),
        FunctionalInequalities.Analysis.selected (fun i => w ((Fin.cons j J' : Fin (k+1) → ι) i)) p =
          if p 0 = true then w j :: FunctionalInequalities.Analysis.selected (fun i => w (J' i)) (Fin.tail p)
            else FunctionalInequalities.Analysis.selected (fun i => w (J' i)) (Fin.tail p) := by
      intro j J' p
      have ht : Fin.tail (fun i => w ((Fin.cons j J' : Fin (k+1) → ι) i)) = fun i => w (J' i) := by
        funext i
        simp [Fin.tail]
      rw [FunctionalInequalities.KLS.BKL.selected_succ, ht]
      simp
    simp only [hsel, FunctionalInequalities.KLS.BKL.tail_not]
    cases hq : q 0 with
    | true =>
      simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h1
      subst h1
      rw [FunctionalInequalities.KLS.BKL.sum_cons_split (k := FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih (Fin.tail q) (fun l₁ l₂ => G (w j :: l₁) l₂) _ _ rfl h2]
      refine Finset.sum_congr rfl fun J₁ _ => ?_
      refine Finset.sum_congr rfl fun J₂ _ => ?_
      simp [List.ofFn_succ]
    | false =>
      simp only [hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h2
      subst h1
      subst h2
      symm
      calc ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i)) + 1) → ι,
              G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i))
          = ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι, ∑ j : ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i))) → ι,
              G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) := by
            refine Finset.sum_congr rfl fun J₁ _ => ?_
            rw [FunctionalInequalities.KLS.BKL.sum_cons_split]
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun J₂ _ => ?_
            simp [List.ofFn_succ]
        _ = ∑ j : ι, ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i))) → ι,
              G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [ih (Fin.tail q) (fun l₁ l₂ => G l₁ (w j :: l₂)) _ _ rfl rfl]
