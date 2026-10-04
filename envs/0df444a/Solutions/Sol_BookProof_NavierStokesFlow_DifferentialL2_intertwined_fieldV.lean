-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.intertwined_fieldV
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:58:42.435157+00:00
-- url     : https://prove2.me/submissions/bbfa7a03-ebfb-48a0-99aa-47c61ff37de3

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.intertwined_fieldV
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_add
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_smul
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_id
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_sum
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sqrtTwo_ne_zero
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_pos
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
theorem solution (i : Fin 3) :
    Intertwined (fieldV A c i)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i) := by

  have hsum : Intertwined (∑ k, ((A i k : ℝ) : ℂ) • pos k)
      (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k)) :=
    Intertwined.sum _ fun k _ => (intertwined_pos k).smul _
  have hid : Intertwined (((c i : ℝ) : ℂ) • LinearMap.id)
      (((c i : ℝ) : ℂ) • LinearMap.id) := Intertwined.id.smul _
  have heq : ((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i
      = (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k))
        + ((c i : ℝ) : ℂ) • LinearMap.id := by
    rw [fieldOp, smul_add, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    · rw [smul_smul]
      congr 1
      have hne := sqrtTwo_ne_zero
      push_cast
      field_simp
  rw [heq]
  exact hsum.add hid
