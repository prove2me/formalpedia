-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:00.108898+00:00
-- url     : https://prove2.me/submissions/8e946f3d-3e5f-47c9-b5d2-07c3eaafde9a

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    SymmetricOn (hermiteDiagDomain lam) (hermiteDiagOp lam) := by

  intro x y
  have hx : (inner ℂ (hermiteDiagOp lam x) (y : L2R) : ℂ)
      = inner ℂ ((mulHamiltonian lam (hermiteDiagRestrict lam x) : L2Nat))
          ((hermiteDiagRestrict lam y : mulSymbolDomain lam) : L2Nat) := by
    rw [← hermiteRepr.inner_map_map (hermiteDiagOp lam x) (y : L2R)]
    congr 1
    simp [hermiteDiagOp]
  have hy : (inner ℂ (x : L2R) (hermiteDiagOp lam y) : ℂ)
      = inner ℂ ((hermiteDiagRestrict lam x : mulSymbolDomain lam) : L2Nat)
          ((mulHamiltonian lam (hermiteDiagRestrict lam y) : L2Nat)) := by
    rw [← hermiteRepr.inner_map_map (x : L2R) (hermiteDiagOp lam y)]
    congr 1
    simp [hermiteDiagOp]
  rw [hx, hy]
  exact mulSymbolOp_symmetric lam lam (fun _ => le_rfl) _ _
