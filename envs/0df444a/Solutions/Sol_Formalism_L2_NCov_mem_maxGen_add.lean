-- Prove2me | solution 1 for Formalism.L2.NCov.mem_maxGen_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:21.981976+00:00
-- url     : https://prove2.me/submissions/e094c453-88b6-4ee1-8e5b-7990512b4117

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_add_pow_apply_eq_zero
import Theorems.Thm_Formalism_L2_NCov_commute_sub_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.NCov
theorem _root_.solution {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A + B).maxGenEigenspace (a + b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨k + l, ?_⟩
  have e : A + B - (a + b) • (1 : End K V) = (A - a • 1) + (B - b • 1) := by
    rw [add_smul]; abel
  rw [e]
  exact add_pow_apply_eq_zero (commute_sub_smul h a b) hk hl
end Formalism.L2.NCov
