-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.unram_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:19.080034+00:00
-- url     : https://prove2.me/submissions/b74befe2-3ffc-4357-bd66-aa4b475c157a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_mem_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isUnitIn_div_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hmem : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp.isPrime, mem_conjIdeal_iff]
    refine ⟨hθ, fun h => hθ ?_⟩
    rw [map_sub, conjO_conjO] at h
    have := p.neg_mem h
    rwa [neg_sub] at this
  have h := (isUnitIn_div_iff hp.isPrime (θ - conjO K θ)
    (one_mem (Formalism.HermitianLatticesTheory.hcompl (K := K) p))).mpr hmem
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at h
end Formalism.HermitianLattices.Ext.L3.WA
