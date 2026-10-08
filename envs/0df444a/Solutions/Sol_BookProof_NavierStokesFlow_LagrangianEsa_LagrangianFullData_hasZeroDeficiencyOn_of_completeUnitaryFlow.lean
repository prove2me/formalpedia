-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:08:42.823004+00:00
-- url     : https://prove2.me/submissions/8e819023-78f1-4346-ae25-82e198bb415e

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_completeUnitaryFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution (U : ℝ → F → F)
    (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v)
    (hUD : ∀ (t : ℝ) (v : L.D), U t (v : F) ∈ L.D)
    (hderiv : ∀ (v : L.D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (L.hFull ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn L.D L.hFull :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
      L.D L.hFull U L.dense hnorm hU0 hUD hderiv
