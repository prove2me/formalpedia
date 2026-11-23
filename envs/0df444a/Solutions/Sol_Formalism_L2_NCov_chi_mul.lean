-- Prove2me | solution 1 for Formalism.L2.NCov.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:57.222661+00:00
-- url     : https://prove2.me/submissions/1a331e72-26e9-44ab-9d9e-425511ea6c37

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_mem_maxGen_mul
import Theorems.Thm_Formalism_L2_NCov_eq_of_le_maxGen
import Theorems.Thm_Formalism_L2_NCov_W_le
import Theorems.Thm_Formalism_L2_NCov_commute_adjoin

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
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {χ : Algebra.adjoin O S → K}
    (hW : W _ χ ≠ ⊥) (s t : Algebra.adjoin O S) : χ (s * t) = χ s * χ t :=
  eq_of_le_maxGen hW (W_le _ χ (s * t)) fun _ hx =>
    mem_maxGen_mul (commute_adjoin hS s.2 t.2) (W_le _ χ s hx) (W_le _ χ t hx)
end Formalism.L2.NCov
