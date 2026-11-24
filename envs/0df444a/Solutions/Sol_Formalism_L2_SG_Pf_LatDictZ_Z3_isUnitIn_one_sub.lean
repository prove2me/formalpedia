-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.isUnitIn_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:37.353345+00:00
-- url     : https://prove2.me/submissions/2235374d-6703-4044-b6bc-ee6ff3e5b14d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a b : K}
    (ha : a ∈ locRing p) (has : star a = a) (hna : ¬ IsUnitIn (locRing p) a) (hb : b ∈ locRing p) :
    IsUnitIn (locRing p) (1 - a * b) := by
  rw [mem_locRing, mem_locR_iff hp] at ha hb
  obtain ⟨r, s, hs, rfl⟩ := ha
  obtain ⟨r', t, ht, rfl⟩ := hb
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have ht0 := algebraMap_ne_zero_of_mem_hcompl hp ht
  have hr : ¬ (r ∉ p ∧ conjO K r ∉ p) := by
    intro hr'
    apply hna
    rw [isUnitIn_div_iff hp r hs, mem_hcompl_iff hp, mem_conjIdeal_iff]
    exact hr'
  have hsc := (mem_hcompl_iff hp s).mp hs
  rw [mem_conjIdeal_iff] at hsc
  have e : star (algebraMap (𝓞 K) K r) * algebraMap (𝓞 K) K s =
      algebraMap (𝓞 K) K r * star (algebraMap (𝓞 K) K s) := by
    rw [star_div₀, div_eq_div_iff (star_ne_zero.mpr hs0) hs0] at has
    exact has
  have hrel : conjO K r * s = r * conjO K s := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (conjO K r * s) = algebraMap (𝓞 K) K (r * conjO K s)
    rw [map_mul, map_mul, algebraMap_conjO, algebraMap_conjO]
    exact e
  have hrp : r ∈ p ∧ conjO K r ∈ p := by
    by_cases h1 : r ∈ p
    · refine ⟨h1, ?_⟩
      have h3 : conjO K r * s ∈ p := by
        rw [hrel]
        exact p.mul_mem_right _ h1
      exact (hp.mem_or_mem h3).resolve_right hsc.1
    · have h2 : conjO K r ∈ p := by
        by_contra h2
        exact hr ⟨h1, h2⟩
      have h3 : r * conjO K s ∈ p := by
        rw [← hrel]
        exact p.mul_mem_right _ h2
      exact absurd ((hp.mem_or_mem h3).resolve_right hsc.2) h1
  have hst : s * t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hs ht
  have htc := (mem_hcompl_iff hp (s * t)).mp hst
  rw [mem_conjIdeal_iff] at htc
  have hnum : s * t - r * r' ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff]
    constructor
    · intro hm
      apply htc.1
      have e1 : s * t = (s * t - r * r') + r * r' := by ring
      rw [e1]
      exact p.add_mem hm (p.mul_mem_right r' hrp.1)
    · intro hm
      apply htc.2
      have e1 : conjO K (s * t) = conjO K (s * t - r * r') + conjO K r * conjO K r' := by
        rw [map_sub, map_mul (conjO K) r r']
        ring
      rw [e1]
      exact p.add_mem hm (p.mul_mem_right _ hrp.2)
  have key := (isUnitIn_div_iff hp _ hst).mpr hnum
  convert key using 1
  simp only [map_sub, map_mul]
  field_simp
end Formalism.L2.SG.Pf.LatDictZ.Z3
