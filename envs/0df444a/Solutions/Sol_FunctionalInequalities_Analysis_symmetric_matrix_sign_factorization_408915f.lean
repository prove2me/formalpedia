-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:37.976408+00:00
-- url     : https://prove2.me/submissions/36d3b90f-aa4b-41f4-beda-ee41dfcca260

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sqrt_real_cfc_bridge_408915f

noncomputable section
open scoped MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteIndex
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
private lemma FunctionalInequalities.Analysis.sign_sq_real (x : ℝ) (hx : x ≠ 0) :
    (SignType.sign x : ℝ) * (SignType.sign x : ℝ) = 1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hnpos : ¬ 0 < x := not_lt_of_ge (le_of_lt hxneg)
    have hs : (SignType.sign x : ℝ) = -1 := by
      simp only [sign_neg hxneg, SignType.coe_neg_one]
    rw [hs]
    norm_num
  · have hnneg : ¬ x < 0 := not_lt_of_ge (le_of_lt hxpos)
    have hs : (SignType.sign x : ℝ) = 1 := by
      simp only [sign_pos hxpos, SignType.coe_one]
    rw [hs]
    norm_num
private lemma FunctionalInequalities.Analysis.sqrt_sqrt_sq_mul_sign_sqrt_sqrt (x : ℝ) :
    Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
        Real.sqrt (Real.sqrt (x * x)) = x := by
  have hsq :
      Real.sqrt (Real.sqrt (x * x)) ^ 2 = Real.sqrt (x * x) :=
    Real.sq_sqrt (Real.sqrt_nonneg (x * x))
  by_cases hx : x = 0
  · subst x
    simp [SignType.sign]
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hnpos : ¬ 0 < x := not_lt_of_ge (le_of_lt hxneg)
      have hs : (SignType.sign x : ℝ) = -1 := by
        simp only [sign_neg hxneg, SignType.coe_neg_one]
      have hsqrt : Real.sqrt (x * x) = -x := by
        rw [show x * x = x ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_neg hxneg]
      rw [hs]
      nlinarith [hsq, hsqrt]
    · have hnneg : ¬ x < 0 := not_lt_of_ge (le_of_lt hxpos)
      have hs : (SignType.sign x : ℝ) = 1 := by
        simp only [sign_pos hxpos, SignType.coe_one]
      have hsqrt : Real.sqrt (x * x) = x := by
        rw [show x * x = x ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos hxpos]
      rw [hs]
      nlinarith [hsq, hsqrt]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The spectral sign factorization used to absorb `sqrt |M|` into the random
vector. No PSD, basis, commutation, factorization, or sign-square identity is
supplied as an assumption. -/
theorem solution
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    let AbsM : Matrix ι ι ℝ := CFC.sqrt (M * M)
    let S : Matrix ι ι ℝ := CFC.sqrt AbsM
    let SignM : Matrix ι ι ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    S * S = AbsM ∧ S * SignM * S = M ∧
      (IsUnit M → SignM * SignM = 1) := by
    dsimp
    obtain ⟨hMM, hsqrt, hroot, hsqrtroot⟩ :=
      FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_408915f M hM
    have hspec : (spectrum ℝ M).Finite :=
      Matrix.finite_real_spectrum (A := M)
    have hcomp (g f : ℝ → ℝ) :
        cfc (fun x => g (f x)) M = cfc g (cfc f M) := by
      exact cfc_comp' g f M
        (hg := (hspec.image f).continuousOn g)
        (hf := hspec.continuousOn f)
    have hcfc_mul (f g : ℝ → ℝ) :
        cfc f M * cfc g M =
          cfc (fun x => f x * g x) M := by
      rw [← cfc_mul (hf := hspec.continuousOn f)
        (hg := hspec.continuousOn g)]
    have hid : cfc (fun x : ℝ => x) M = M := by
      change cfc id M = M
      exact cfc_id ℝ M hM
    have hone : cfc (fun _ : ℝ => (1 : ℝ)) M = 1 := by
      change cfc (1 : ℝ → ℝ) M = 1
      exact cfc_one ℝ M hM
    have hsq : cfc (fun x : ℝ => x * x) M = M * M := by
      calc
        cfc (fun x : ℝ => x * x) M =
            cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x) M :=
          (hcfc_mul (fun x : ℝ => x) (fun x : ℝ => x)).symm
        _ = M * M := by rw [hid]
    have hAbs :
        CFC.sqrt (M * M) =
          cfc (fun x : ℝ => Real.sqrt (x * x)) M := by
      calc
        CFC.sqrt (M * M) =
            cfc (fun x : ℝ => Real.sqrt x) (M * M) := hsqrt
        _ = cfc (fun x : ℝ => Real.sqrt x)
            (cfc (fun x : ℝ => x * x) M) := by rw [hsq]
        _ = cfc (fun x : ℝ => Real.sqrt (x * x)) M := by
          simpa [Function.comp_def] using
            (hcomp (fun x : ℝ => Real.sqrt x) (fun x : ℝ => x * x)).symm
    have hS :
        CFC.sqrt (CFC.sqrt (M * M)) =
          cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
      calc
        CFC.sqrt (CFC.sqrt (M * M)) =
            cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) :=
          hsqrtroot
        _ = cfc (fun x : ℝ => Real.sqrt x)
            (cfc (fun x : ℝ => Real.sqrt (x * x)) M) := by rw [hAbs]
        _ = cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
          simpa [Function.comp_def] using
            (hcomp (fun x : ℝ => Real.sqrt x)
              (fun x : ℝ => Real.sqrt (x * x))).symm
    have hprod :
        cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M =
          cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := by
      calc
        cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M =
            cfc
                (fun x : ℝ =>
                  Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ)) M *
              cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hcfc_mul]
        _ = cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hcfc_mul]
    have hfactor :
        CFC.sqrt (CFC.sqrt (M * M)) *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            CFC.sqrt (CFC.sqrt (M * M)) = M := by
      calc
        CFC.sqrt (CFC.sqrt (M * M)) *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            CFC.sqrt (CFC.sqrt (M * M)) =
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
              cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
              cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hS]
        _ = cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := hprod
        _ = cfc (fun x : ℝ => x) M := by
          apply cfc_congr
          intro x hx
          exact sqrt_sqrt_sq_mul_sign_sqrt_sqrt x
        _ = M := hid
    refine ⟨CFC.sqrt_mul_sqrt_self (CFC.sqrt (M * M)) hroot, hfactor, ?_⟩
    intro hunit
    have hzero : (0 : ℝ) ∉ spectrum ℝ M :=
      spectrum.zero_notMem ℝ hunit
    have hsignsq :
        cfc (fun x : ℝ => (SignType.sign x : ℝ) *
          (SignType.sign x : ℝ)) M =
          cfc (fun _ : ℝ => (1 : ℝ)) M := by
      apply cfc_congr
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hx'
        subst x
        exact hzero hx
      exact sign_sq_real x hx0
    calc
      cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
          cfc (fun x : ℝ => (SignType.sign x : ℝ)) M =
          cfc (fun x : ℝ => (SignType.sign x : ℝ) *
            (SignType.sign x : ℝ)) M :=
        hcfc_mul (fun x : ℝ => (SignType.sign x : ℝ))
          (fun x : ℝ => (SignType.sign x : ℝ))
      _ = cfc (fun _ : ℝ => (1 : ℝ)) M := hsignsq
      _ = 1 := hone
