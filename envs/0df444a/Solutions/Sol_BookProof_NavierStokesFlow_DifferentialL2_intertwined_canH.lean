-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T04:00:07.506318+00:00
-- url     : https://prove2.me/submissions/9e63239c-cbaf-459c-9662-86093d74a985

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_add
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_smul
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_comp
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_sum
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sqrtTwo_ne_zero
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_mom
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_fieldV
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
theorem solution :
    Intertwined (canH A c) (nsDiffH A (fun j => Real.sqrt 2 * c j)) := by

  have hscal : ((Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    have hne := sqrtTwo_ne_zero
    push_cast
    field_simp
  have hterm : ∀ i : Fin 3,
      Intertwined (((1 : ℂ) / 2) • ((mom i).comp (fieldV A c i) + (fieldV A c i).comp (mom i)))
        (((1 : ℂ) / 2) • ((momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i))) := by
    intro i
    have hm := intertwined_mom i
    have hf := intertwined_fieldV A c i
    have h := ((hm.comp hf).add (hf.comp hm)).smul ((1 : ℂ) / 2)
    have heq : (((Real.sqrt 2 : ℝ) : ℂ) • momOp i).comp
          (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i)
        + (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i).comp
          (((Real.sqrt 2 : ℝ) : ℂ) • momOp i)
        = (momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, smul_smul, hscal, mul_comm (((1 / Real.sqrt 2 : ℝ) : ℂ))
          (((Real.sqrt 2 : ℝ) : ℂ)), hscal, one_smul, one_smul]
    rw [← heq]
    exact h
  exact Intertwined.sum Finset.univ fun i _ => hterm i
