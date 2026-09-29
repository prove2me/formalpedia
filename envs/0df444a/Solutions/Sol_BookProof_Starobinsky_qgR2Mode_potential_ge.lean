-- Prove2me | solution 1 for BookProof.Starobinsky.qgR2Mode_potential_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:55:20.171659+00:00
-- url     : https://prove2.me/submissions/199cb0a9-cdf6-42ed-83cc-c30c1e2d03d9

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.qgR2Mode_potential_ge
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_Starobinsky_confV_ge
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.Starobinsky












open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (halpha : 0 < alpha) (k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgR2ModePotential M alpha Rc k := confV_ge halpha (Rc k)
