-- Prove2me | solution 1 for BookProof.Starobinsky.confV_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:55:19.097144+00:00
-- url     : https://prove2.me/submissions/a360eb16-0214-46ff-bbfe-14232d41058b

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.confV_bddBelow
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

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) :
    BddBelow (Set.range fun Rc => confV M alpha Rc) := ⟨-(M ^ 4 / (16 * alpha)), by rintro _ ⟨Rc, rfl⟩; exact confV_ge halpha Rc⟩
