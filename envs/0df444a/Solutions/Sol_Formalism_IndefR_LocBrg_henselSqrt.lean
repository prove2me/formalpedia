-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.henselSqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:32.576831+00:00
-- url     : https://prove2.me/submissions/6b26ae70-ec70-41f3-8ca5-b637131b0e6d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
import Theorems.Thm_Formalism_IndefR_LocBrg_pow_small
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_bound
import Theorems.Thm_Formalism_IndefR_LocBrg_pow_anti
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_cauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
namespace Formalism.IndefR.LocBrg
theorem _root_.solution : HenselSqrt := by
  intro L _ _ _ h2 u hu
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete (newton_cauchy u h2 hu)
  have hsq : Filter.Tendsto (fun k => newtonSq u k * newtonSq u k) Filter.atTop (nhds (s * s)) := hs.mul hs
  refine ⟨s, ?_, ?_⟩
  · by_contra hne
    have hne' : s * s - u ≠ 0 := sub_ne_zero.mpr hne
    have hv0 : Valued.v (s * s - u) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne'
    have hr0 : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s * s - u) ≠ 0 := by
      intro h
      apply hv0
      rw [← Valuation.embedding_restrict, h, map_zero]
    have h1 := hsq.eventually_mem (Valued.mem_nhds.mpr ⟨Units.mk0 _ hr0, subset_rfl⟩)
    obtain ⟨N, hN⟩ := pow_small hu (Units.mk0 _ hv0)
    rw [Units.val_mk0] at hN
    obtain ⟨m, hm1, hm2⟩ := (h1.and (Filter.eventually_ge_atTop N)).exists
    have hm1' : Valued.v (newtonSq u m * newtonSq u m - s * s) < Valued.v (s * s - u) := by
      have h5 := hm1
      simp only [Set.mem_setOf_eq, Units.val_mk0] at h5
      exact (Valuation.restrict_lt_iff _).mp h5
    have hb := (newton_bound u h2 hu m).2
    have h3 : Valued.v (newtonSq u m * newtonSq u m - u) < Valued.v (s * s - u) :=
      lt_of_le_of_lt (hb.trans (pow_anti hu.le (by omega))) hN
    have he : s * s - u = -((newtonSq u m * newtonSq u m) - s * s) + (newtonSq u m * newtonSq u m - u) := by
      ring
    have h4 : Valued.v (-((newtonSq u m * newtonSq u m) - s * s) + (newtonSq u m * newtonSq u m - u)) <
        Valued.v (s * s - u) := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ h3)
      rw [Valuation.map_neg]
      exact hm1'
    rw [← he] at h4
    exact lt_irrefl _ h4
  · have h1 := hs.eventually_mem (Valued.mem_nhds.mpr ⟨1, subset_rfl⟩)
    obtain ⟨m, hm⟩ := h1.exists
    have hm' : Valued.v (newtonSq u m - s) < 1 := by
      have h5 := hm
      simp only [Set.mem_setOf_eq, Units.val_one] at h5
      exact (Valuation.restrict_lt_one_iff _).mp h5
    have hb := (newton_bound u h2 hu m).1
    have he : s - 1 = -(newtonSq u m - s) + (newtonSq u m - 1) := by ring
    rw [he]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hb)
    rw [Valuation.map_neg]
    exact hm'
end Formalism.IndefR.LocBrg
