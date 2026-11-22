-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.algebraMap_mem_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:43.519137+00:00
-- url     : https://prove2.me/submissions/16bcfdd7-6a1e-45ef-afd4-c9ac9e3332c2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locRing
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Formalism.HermitianLatticesTheory.locDual_alg_mem r⟩
end Formalism.HermitianLattices.Ext.L3.WA
