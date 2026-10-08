-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:05.785811+00:00
-- url     : https://prove2.me/submissions/18cc4982-08b4-4c2c-9563-9863b508dff3

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_completeUnitaryFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in
theorem solution (U : ℝ → F → F)
    (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v)
    (hUD : ∀ (t : ℝ) (v : d.D), U t (v : F) ∈ d.D)
    (hderiv : ∀ (v : d.D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F))
        (Complex.I • (d.hamiltonian ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
      d.D d.hamiltonian U d.dense hnorm hU0 hUD hderiv
