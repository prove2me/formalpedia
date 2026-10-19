-- Prove2me | solution 1 for BookProof.WallEsaBddBelow.wallHam_add_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T06:15:43.538989+00:00
-- url     : https://prove2.me/submissions/d9193c8f-e779-4a95-bbf7-f348710ad50f

-- Generated from ChapterWallEsaBddBelow.lean — solution of BookProof.WallEsaBddBelow.wallHam_add_const
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
import Theorems.Thm_BookProof_ScalaronEsa_mulCc_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
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

theorem solution (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (c : ℝ) :
    wallHam (fun x => V x + c) (hV.add contDiff_const)
      = wallHam V hV + ((constOp c).toLinearMap ∘ₗ (ccDomain ℝ).subtype) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective x
  have hpot : opCc (fun x => V x + c) (hV.add contDiff_const) (ccEquiv ℝ f)
      = opCc V hV (ccEquiv ℝ f) + constOp c ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 _) := by
    rw [opCc_apply, opCc_apply, ccEquiv_coe]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [(mulCc (fun x => V x + c) (hV.add contDiff_const) f).coeFn_toLp 2
        (volume : Measure ℝ),
      (mulCc V hV f).coeFn_toLp 2 (volume : Measure ℝ),
      (f : 𝓢(ℝ, ℂ)).coeFn_toLp 2 (volume : Measure ℝ),
      MeasureTheory.Lp.coeFn_add ((mulCc V hV f).toLp 2 (volume : Measure ℝ))
        (constOp c ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ))),
      MeasureTheory.Lp.coeFn_smul ((c : ℂ))
        ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ))] with x h1 h2 h3 h4 h5
    have h5' : ((constOp c ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ)) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
        = (c : ℂ) * (((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x := by
      rw [constOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      simpa using h5
    rw [h1, h4, Pi.add_apply, h2, h5', h3]
    simp only [mulCc_apply]
    push_cast
    ring
  simp only [wallHam, LinearMap.add_apply, hpot, LinearMap.coe_comp, Function.comp_apply,
    Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  abel
