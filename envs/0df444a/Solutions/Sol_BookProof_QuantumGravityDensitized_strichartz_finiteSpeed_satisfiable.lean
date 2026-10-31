-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:50:13.588914+00:00
-- url     : https://prove2.me/submissions/4a1c3552-d6b4-4a7d-82bb-0ad36a837b50

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Theorems.Thm_BookProof_QuantumGravityDensitized_qgModeHamiltonian_deficiencyTrivialAt
import Theorems.Thm_BookProof_QuantumGravityDensitized_strichartz_esa_of_finiteSpeed
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) := strichartz_esa_of_finiteSpeed _ fun _ hz => qgModeHamiltonian_deficiencyTrivialAt a b V hz
