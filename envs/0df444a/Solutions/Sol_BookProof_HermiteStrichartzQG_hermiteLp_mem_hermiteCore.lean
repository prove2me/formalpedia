-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteLp_mem_hermiteCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T11:01:26.100686+00:00
-- url     : https://prove2.me/submissions/2d896389-476d-4cb6-8a92-4612eebf3e30

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteLp_mem_hermiteCore
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : hermiteLp n ∈ hermiteCore := Submodule.subset_span ⟨n, rfl⟩
