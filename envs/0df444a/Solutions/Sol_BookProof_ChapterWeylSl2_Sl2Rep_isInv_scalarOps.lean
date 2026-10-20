-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:04:46.748922+00:00
-- url     : https://prove2.me/submissions/550b9c2e-44fd-4313-90c2-ff660fb2d8b6

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

theorem w_ad_mem {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Submodule ℂ V}
    (a : Module.End ℂ V) (ha : ∀ x ∈ W, a x ∈ W) (f : Module.End ℂ V)
    (hf : f ∈ BookProof.ChapterWeylSl2.Sl2Rep.scalarOps W) :
    BookProof.ChapterWeylSl2.Sl2Rep.ad a f ∈ BookProof.ChapterWeylSl2.Sl2Rep.scalarOps W := by
  obtain ⟨hf1, c, hf2⟩ := hf
  refine ⟨fun v => ?_, 0, fun w hw => ?_⟩
  · rw [BookProof.ChapterWeylSl2.Sl2Rep.ad_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact W.sub_mem (ha _ (hf1 v)) (hf1 _)
  · rw [BookProof.ChapterWeylSl2.Sl2Rep.ad_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, hf2 w hw, hf2 _ (ha w hw), map_smul, sub_self, zero_smul]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}
open BookProof.ChapterWeylSl2.Sl2Rep in
theorem solution {R : Sl2Rep V} {W : Submodule ℂ V} (hW : R.IsInv W) :
    (adRep R).IsInv (scalarOps W) := by
  obtain ⟨hE, hF, hH⟩ := hW
  exact ⟨fun f hf => w_ad_mem _ hE f hf, fun f hf => w_ad_mem _ hF f hf, fun f hf => w_ad_mem _ hH f hf⟩
