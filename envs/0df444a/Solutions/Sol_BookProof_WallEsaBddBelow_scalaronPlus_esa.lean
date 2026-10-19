-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.scalaronPlus_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T11:58:27.53838+00:00
-- url     : https://prove2.me/submissions/35f5e7ac-a532-4e04-9b86-4ee189a666ec

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.scalaronPlus_esa
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_essentiallySelfAdjoint_of_bddBelow
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.WallEsaBddBelow




open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.Starobinsky

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {c : ℝ} (hWc : ∀ x, -c ≤ W x) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun phi => BookProof.Starobinsky.starobinskyV M alpha phi + W phi)
        ((BookProof.ScalaronEsa.contDiff_starobinskyV M alpha).add hW)) :=
  wallHam_essentiallySelfAdjoint_of_bddBelow _ _
    (c := c) fun phi => by
      have h1 := BookProof.Starobinsky.starobinskyV_nonneg (M := M) halpha phi
      have h2 := hWc phi
      linarith
