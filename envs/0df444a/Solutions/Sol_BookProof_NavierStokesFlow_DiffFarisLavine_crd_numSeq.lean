-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:02.791552+00:00
-- url     : https://prove2.me/submissions/b8febaea-e97c-483f-aa88-62de1f505553

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

@[simp] private theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (ann i x) = aFun i (crd x) := rfl
@[simp] private theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (cre i x) = cFun i (crd x) := rfl
@[simp] private theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := by
  funext β; simp [crd]
@[simp] private theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := by
  funext β; simp [crd]

theorem solution (i : Fin 3) (x : lpFiniteModes Vel) (β : Vel) :
    crd (numSeq i x) β = ((β i : ℝ) : ℂ) * crd x β := by
  by_cases h : β i = 0
  · simp [numSeq, cFun, h]
  · have h1 : 1 ≤ β i := Nat.one_le_iff_ne_zero.mpr h
    have hlow : ((lower i β) i : ℝ) + 1 = (β i : ℝ) := by
      rw [lower_self]
      have : (1 : ℕ) ≤ β i := h1
      push_cast [Nat.cast_sub this]
      ring
    have hraise : raise i (lower i β) = β := raise_lower i h1
    have hsq : (Real.sqrt ((β i : ℝ))) * (Real.sqrt (((lower i β) i : ℝ) + 1)) = (β i : ℝ) := by
      rw [hlow, ← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (β i : ℝ))]
      rw [Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (β i : ℝ))]
      exact (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (β i : ℝ)))
    simp only [numSeq, LinearMap.comp_apply, crd_cre, crd_ann, cFun, aFun, hraise]
    rw [← mul_assoc, ← Complex.ofReal_mul, hsq]

#print axioms solution
