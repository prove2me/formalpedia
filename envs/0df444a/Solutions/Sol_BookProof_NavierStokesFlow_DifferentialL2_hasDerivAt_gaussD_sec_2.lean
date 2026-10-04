-- Prove2me | solution 2 for BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_gaussD_sec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:24:21.030646+00:00
-- url     : https://prove2.me/submissions/3ecd8be8-44f7-4d23-a9a5-a88678ea4672

import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore

set_option autoImplicit false

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem norm_sq_sec_aux_887b {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [sec, Function.update_of_ne hji]
  · simp [sec]

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem solution {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by
  have key : (fun s : ℝ => gaussD (sec i x s)) =
      fun s => Real.exp (-((∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + s ^ 2) / 4) := by
    funext s
    show Real.exp (-‖sec i x s‖ ^ 2 / 4) = _
    rw [norm_sq_sec_aux_887b]
  rw [key]
  have h := (((hasDerivAt_pow 2 t).const_add
    (∑ j ∈ Finset.univ.erase i, (x j) ^ 2)).neg.div_const 4).exp
  convert h using 1
  show -(t / 2) * Real.exp (-‖sec i x t‖ ^ 2 / 4) = _
  rw [norm_sq_sec_aux_887b]
  norm_num
  ring
  rfl
