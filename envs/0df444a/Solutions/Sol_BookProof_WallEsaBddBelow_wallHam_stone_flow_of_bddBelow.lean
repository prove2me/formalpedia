-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T06:15:45.846981+00:00
-- url     : https://prove2.me/submissions/a80fe82d-16a6-417a-b8e4-4df6ebc0a751

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_essentiallySelfAdjoint_of_bddBelow
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.WallEsaBddBelow




open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.StoneBridge

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ)))
      (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))),
      IsSelfAdjointExtension (wallHam V hV) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (wallHam_symmetricOn V hV)
    (wallHam_essentiallySelfAdjoint_of_bddBelow V hV hVc)
