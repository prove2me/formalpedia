-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.isUnitIn_div_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:02.455057+00:00
-- url     : https://prove2.me/submissions/f3f15e42-2e7d-4379-a676-d9b18920715b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locRing
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
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := fun h => h0 (by rw [h, zero_div])
    rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv
    obtain ⟨u, hu, h1⟩ := hinv
    obtain ⟨v, hv⟩ := Submodule.mem_one.mp h1
    have e : u * s = v * r := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u * s) = algebraMap (𝓞 K) K (v * r)
      rw [map_mul, map_mul, hv, inv_div]
      field_simp
    have hus := (mem_hcompl_iff hp _).mp (mul_mem hu hs)
    rw [e] at hus
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hus.1 (p.mul_mem_left v h), fun h => hus.2 (Ideal.mul_mem_left _ v h)⟩
  · intro hr
    have hr0 := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hr0 hs0, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, inv_div _ _⟩
end Formalism.HermitianLattices.Ext.L3.WA
