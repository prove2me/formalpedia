-- Prove2me | solution 1 for BookProof.Starobinsky.mulSymbolDomain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:18.416892+00:00
-- url     : https://prove2.me/submissions/fd672afe-d728-4f0e-9d61-af6eeb001ef1

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.mulSymbolDomain_dense
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_Starobinsky_lpFiniteModes_le_mulSymbolDomain
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.Starobinsky












open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    Dense ((mulSymbolDomain lam : Submodule ℂ L2Nat) : Set L2Nat) := lpFiniteModes_dense.mono (by exact_mod_cast lpFiniteModes_le_mulSymbolDomain lam)
