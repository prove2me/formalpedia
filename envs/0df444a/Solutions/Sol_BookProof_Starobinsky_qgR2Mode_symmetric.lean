-- Prove2me | solution 1 for BookProof.Starobinsky.qgR2Mode_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:42:35.489688+00:00
-- url     : https://prove2.me/submissions/64938004-4796-4885-94d9-23576b6cce72

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.qgR2Mode_symmetric
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_symmetric
open BookProof.Starobinsky












open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution :
    SymmetricOn (mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)))
      (qgR2ModeHamiltonian a b M alpha Rc) := mulSymbolOp_symmetric _ _ (fun _ => le_rfl)
