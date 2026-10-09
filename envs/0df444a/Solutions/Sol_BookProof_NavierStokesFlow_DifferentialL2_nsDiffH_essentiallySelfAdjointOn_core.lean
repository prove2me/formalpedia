-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:15.577742+00:00
-- url     : https://prove2.me/submissions/e182a161-0e12-46f5-a6b4-f93e1c5a5a5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_canH
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canH_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_embedCore_coe
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_hasZeroDeficiencyOn_map_of_linearIsometryEquiv
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
theorem solution :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by

  rw [essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn]
  have hc : (fun j => Real.sqrt 2 * (c j / Real.sqrt 2)) = c := by
    funext j
    field_simp
  have hint : ∀ x : lpFiniteModes Vel,
      ((nsDiffH A c ⟨velUnitary ((x : L2I Vel)), velUnitary_mem_core x⟩ :
            polyGaussCore (d := 3)) : L2d 3)
        = velUnitary (((canH A (fun j => c j / Real.sqrt 2) x : lpFiniteModes Vel) : L2I Vel)) := by
    intro x
    have h := intertwined_canH A (fun j => c j / Real.sqrt 2) x
    rw [hc] at h
    have hx : (⟨velUnitary ((x : L2I Vel)), velUnitary_mem_core x⟩ : polyGaussCore (d := 3))
        = embedCore x := rfl
    rw [hx, h, embedCore_coe]
  refine hasZeroDeficiencyOn_map_of_linearIsometryEquiv velUnitary velUnitary_mem_core hint ?_
  exact (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn _ _).1
    (canH_essentiallySelfAdjointOn_core A (fun j => c j / Real.sqrt 2))
