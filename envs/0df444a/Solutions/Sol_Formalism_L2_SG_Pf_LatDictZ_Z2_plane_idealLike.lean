-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.plane_idealLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:26.114161+00:00
-- url     : https://prove2.me/submissions/af497e0b-7d01-4ba3-8800-3485e493d77a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locR_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (I : Ideal (𝓞 K))
    (hI : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ∉ I) : IdealLike (locRing p) (InI p I) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ ⟨r₁, s₁, hs₁, hr₁, rfl⟩ ⟨r₂, s₂, hs₂, hr₂, rfl⟩
    have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
    have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
    refine ⟨r₁ * s₂ - s₁ * r₂, s₁ * s₂, mul_mem hs₁ hs₂,
      I.sub_mem (I.mul_mem_right _ hr₁) (I.mul_mem_left _ hr₂), ?_⟩
    rw [div_sub_div _ _ h1 h2, map_sub, map_mul, map_mul, map_mul]
  · intro x hx a ha
    obtain ⟨r, s, hs, hr, rfl⟩ := ha
    obtain ⟨k, t, ht, rfl⟩ := (mem_locR_iff hp x).1 ((mem_locRing p x).1 hx)
    refine ⟨k * r, t * s, mul_mem ht hs, I.mul_mem_left k hr, ?_⟩
    rw [div_mul_div_comm, map_mul, map_mul]
  · rintro ⟨r, s, hs, hr, h1⟩
    have h0 := algebraMap_ne_zero_of_mem_hcompl hp hs
    rw [eq_div_iff h0, one_mul] at h1
    have hsr : s = r := RingOfIntegers.ext h1
    exact hI s hs (hsr ▸ hr)
end Formalism.L2.SG.Pf.LatDictZ.Z2
