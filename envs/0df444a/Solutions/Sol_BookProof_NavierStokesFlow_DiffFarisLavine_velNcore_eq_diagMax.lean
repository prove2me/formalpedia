-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:10:58.816194+00:00
-- url     : https://prove2.me/submissions/d7ffa47c-daf3-4dab-8b6f-b0ec9cb26cd9

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

private theorem crd_numSeq (i : Fin 3) (x : lpFiniteModes Vel) (β : Vel) :
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
theorem solution (mu : ℝ) (x : lpFiniteModes Vel) :
    ((velNcore mu x : lpFiniteModes Vel) : L2I Vel)
      = (diagMax (velSym mu)
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel) := by
  refine lp.ext (funext fun β => ?_)
  have hleft : (((velNcore mu x : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β
      = ((2 * mu : ℝ) : ℂ) * (∑ _i : Fin 3, ((β _i : ℝ) : ℂ) * crd x β)
        + ((3 * mu + 1 : ℝ) : ℂ) * crd x β := by
    simp only [velNcore, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h1 : crd ((((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) x
        + (((3 * mu + 1 : ℝ) : ℂ)) • x) β
        = ((2 * mu : ℝ) : ℂ) * crd ((∑ i, numSeq i) x) β
          + ((3 * mu + 1 : ℝ) : ℂ) * crd x β := by
      simp [crd_add, crd_smul]
    have h2 : crd ((∑ i, numSeq i) x) β = ∑ i, ((β i : ℝ) : ℂ) * crd x β := by
      rw [LinearMap.sum_apply]
      have : ∀ s : Finset (Fin 3), crd (∑ i ∈ s, numSeq i x) β
          = ∑ i ∈ s, crd (numSeq i x) β := by
        intro s
        induction s using Finset.induction with
        | empty => simp [crd]
        | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, crd_add]; simp [ih]
      rw [this]
      exact Finset.sum_congr rfl fun i _ => crd_numSeq i x β
    change crd ((((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) x
        + (((3 * mu + 1 : ℝ) : ℂ)) • x) β = _
    rw [h1, h2]
  have hstep : (∑ _i : Fin 3, ((β _i : ℝ) : ℂ) * crd x β) = ((total β : ℕ) : ℂ) * crd x β := by
    rw [← Finset.sum_mul]
    congr 1
    simp only [total, Nat.cast_sum]
    push_cast
    rfl
  have hright : ((diagMax (velSym mu)
        (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel) : Vel → ℂ) β
      = ((velSym mu β : ℝ) : ℂ) * crd x β := rfl
  rw [hleft, hstep, hright]
  simp only [velSym]
  push_cast
  ring

/-! ## The differential comparison operator -/

#print axioms solution
