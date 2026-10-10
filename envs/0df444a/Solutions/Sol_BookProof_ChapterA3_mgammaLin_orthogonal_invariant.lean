-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaLin_orthogonal_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:02.912663+00:00
-- url     : https://prove2.me/submissions/588af43f-7988-4e87-842e-f44beab8bede

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgammaLin_orthogonal_invariant
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_adjoint_mgammaLin
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {W : Submodule ℂ MajoranaSpace}
    (hW : ∀ μ, ∀ x ∈ W, mgammaLin μ x ∈ W) (μ : Fin 4) {y : MajoranaSpace} (hy : y ∈ Wᗮ) :
    mgammaLin μ y ∈ Wᗮ := by

  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← LinearMap.adjoint_inner_left (mgammaLin μ) y u, adjoint_mgammaLin]
  simp only [LinearMap.smul_apply, inner_smul_left]
  rw [(Submodule.mem_orthogonal W y).mp hy _ (hW μ u hu)]
  ring
