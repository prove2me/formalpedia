-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T06:15:44.682814+00:00
-- url     : https://prove2.me/submissions/ab6f7a8c-b54c-4871-8fb9-70368e4240cb

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Theorems.Thm_BookProof_WallEsaBddBelow_constOp_symmetric
import Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_add_const
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn
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
theorem solution (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by
  have hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => V x + c := hV.add contDiff_const
  have hnn : ∀ x, 0 ≤ V x + c := fun x => by linarith [hVc x]
  have hesa := wallHam_essentiallySelfAdjoint (fun x => V x + c) hW hnn
  have hsymm := wallHam_symmetricOn (fun x => V x + c) hW
  have hkey := essentiallySelfAdjointOn_add_bounded (wallHam (fun x => V x + c) hW) hsymm hesa
    (constOp (-c)) (constOp_symmetric (-c))
  have hid : wallHam (fun x => V x + c) hW
      + ((constOp (-c)).toLinearMap ∘ₗ (ccDomain ℝ).subtype) = wallHam V hV := by
    have h := wallHam_add_const V hV c
    refine LinearMap.ext fun x => ?_
    have hx := congrArg (fun T : ccDomain ℝ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) => T x) h
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.subtype_apply, ContinuousLinearMap.coe_coe, constOp,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hx ⊢
    rw [hx]
    push_cast
    module
  rwa [hid] at hkey
