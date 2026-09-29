-- Prove2me | solution 1 for BookProof.YangMillsHermite.idxA_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:55:18.356595+00:00
-- url     : https://prove2.me/submissions/b97a5ba8-8d4d-452e-9138-36a3a0d79cc0

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.idxA_injective
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
theorem solution : Function.Injective (fun p : Fin 3 × Fin 8 => idxA p.1 p.2) := by

  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  have := congrArg Fin.val h
  simp only [idxA] at this
  have hj : j.val = j'.val := by omega
  have ha : a.val = a'.val := by omega
  simp [Fin.ext_iff, hj, ha]
