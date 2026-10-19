-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.oscillatorPlus_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T06:15:46.993975+00:00
-- url     : https://prove2.me/submissions/eb960bcb-e2b9-47cd-ac22-972d74a763ba

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.oscillatorPlus_esa
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_essentiallySelfAdjoint_of_bddBelow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.WallEsaBddBelow




open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun x => x ^ 2 / 4 + V x)
        (((contDiff_id.pow 2).div_const 4).add hV)) :=
  wallHam_essentiallySelfAdjoint_of_bddBelow _ _ (c := c) fun x => by
    have h1 : (0 : ℝ) ≤ x ^ 2 / 4 := by positivity
    have h2 := hVc x
    linarith
