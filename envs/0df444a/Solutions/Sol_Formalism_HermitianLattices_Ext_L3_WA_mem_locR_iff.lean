-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.mem_locR_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:17.456268+00:00
-- url     : https://prove2.me/submissions/ef9f8d14-1300-4f87-b795-72e420571b68

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
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
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) :
    a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ↔
      ∃ r : 𝓞 K, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
        a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  constructor
  · rintro ⟨s, hs, h1⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
    refine ⟨r, s, hs, ?_⟩
    rw [eq_div_iff (algebraMap_ne_zero_of_mem_hcompl hp hs), hr, mul_comm]
  · rintro ⟨r, s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_div_cancel₀ _ (algebraMap_ne_zero_of_mem_hcompl hp hs)]
    exact Formalism.HermitianLatticesTheory.locDual_alg_mem r
end Formalism.HermitianLattices.Ext.L3.WA
