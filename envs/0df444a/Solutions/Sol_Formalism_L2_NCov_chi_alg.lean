-- Prove2me | solution 1 for Formalism.L2.NCov.chi_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:18.368922+00:00
-- url     : https://prove2.me/submissions/dff01eca-a242-4565-a4d3-7c5b8e265ce8

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_maxGen_smul_one
import Theorems.Thm_Formalism_L2_NCov_eq_of_le_maxGen
import Theorems.Thm_Formalism_L2_NCov_W_le
import Theorems.Thm_Formalism_L2_NCov_algebraMap_end_eq

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
theorem _root_.solution {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (c : O) :
    χ (algebraMap O (Algebra.adjoin O S) c) = algebraMap O K c := by
  refine eq_of_le_maxGen hW (W_le _ χ _) ?_
  rw [Subalgebra.coe_algebraMap, algebraMap_end_eq, maxGen_smul_one]
  exact le_top
end Formalism.L2.NCov
