-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.inJ_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:11.086268+00:00
-- url     : https://prove2.me/submissions/691b0df2-c8a9-4786-a2d4-3761893b3a20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_conjO_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isUnitIn_div_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locR_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hfix : star a = a)
    (hnu : ¬ IsUnitIn (locRing p) a) : InJ p a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  have hr : r ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := fun h => hnu ((isUnitIn_div_iff hp r hs).2 h)
  rw [mem_hcompl_iff hp] at hr
  have hs' := (mem_hcompl_iff hp s).1 hs
  have hcs := (mem_hcompl_iff hp _).1 (conjO_mem_hcompl hs)
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hcs0 := algebraMap_ne_zero_of_mem_hcompl hp (conjO_mem_hcompl hs)
  have key : conjO K r * s = r * conjO K s := by
    apply RingOfIntegers.ext
    have e1 := hfix
    rw [star_div₀, ← algebraMap_conjO, ← algebraMap_conjO] at e1
    have e2 : algebraMap (𝓞 K) K (conjO K r) * algebraMap (𝓞 K) K s =
        algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K (conjO K s) := by
      rw [div_eq_div_iff hcs0 hs0] at e1
      exact e1
    simpa [map_mul] using e2
  refine ⟨r, s, hs, ?_, ?_, rfl⟩
  · by_contra hrp
    have hrc : r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
      by_contra h'; exact hr ⟨hrp, h'⟩
    rw [mem_conjIdeal_iff] at hrc
    have h1 : conjO K r * s ∈ p := p.mul_mem_right _ hrc
    rw [key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrp h
    · exact hcs.1 h
  · by_contra hrc
    have hrp : r ∈ p := by
      by_contra h'; exact hr ⟨h', hrc⟩
    have h1 : r * conjO K s ∈ p := p.mul_mem_right _ hrp
    rw [← key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrc ((mem_conjIdeal_iff p r).2 h)
    · exact hs'.1 h
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
