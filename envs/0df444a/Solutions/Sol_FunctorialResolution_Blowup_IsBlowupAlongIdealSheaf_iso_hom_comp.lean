-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.iso_hom_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:19.179697+00:00
-- url     : https://prove2.me/submissions/4bb83f1f-021e-42a2-9cc3-f17b36545b15

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' X'' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (e : X'' ≅ X') : IsBlowupAlongIdealSheaf (e.hom ≫ π) I := by
  have hcomp : I.comap (e.hom ≫ π) = (I.comap π).comap e.hom := by
    simp [Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact h.1.comap_iso e
  · intro W g hg
    obtain ⟨k, hk, hk'⟩ := h.2 W g hg
    refine ⟨k ≫ e.inv, ?_, ?_⟩
    · show (k ≫ e.inv) ≫ e.hom ≫ π = g
      rw [Category.assoc, ← Category.assoc e.inv e.hom π, e.inv_hom_id, Category.id_comp, hk]
    · intro m hm
      have hm' : m ≫ e.hom ≫ π = g := hm
      have hme : m ≫ e.hom = k := hk' _ ((Category.assoc m e.hom π).trans hm')
      rw [← hme, Category.assoc, e.hom_inv_id, Category.comp_id]
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
