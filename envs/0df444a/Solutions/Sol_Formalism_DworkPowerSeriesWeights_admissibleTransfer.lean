-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.admissibleTransfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:22.192418+00:00
-- url     : https://prove2.me/submissions/7900348c-ca02-4d80-969a-a6673f7674eb

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_torus
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_torus
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_entLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_defectOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_defectTwo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_defectOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_defectTwo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_of_noLow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_integral_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_logExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Transfer
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : TransferB := by
  intro F K _ _ _ _ φ hφ l d N0 N1 _ K0 ζ be
  refine ⟨?_, ?_, ?_, fun U hU => integral_map φ hφ hU⟩
  · intro hU a ha ha0
    obtain ⟨b, hb, rfl⟩ := Subfield.mem_map.mp ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at ha0
    obtain ⟨k, hk⟩ := hU b hb hb0
    exact ⟨k, by rw [hφ, hk, ← map_natCast φ l, hφ]⟩
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7⟩⟩
    have hcc : MvPowerSeries.constantCoeff be = 0 := cc_of_noLow h3
    have E1 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de1 be))) := by
      rw [← map_defectOne, map_logExp φ l (constantCoeff_defectOne hcc)]
    have E2 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de2 be))) := by
      rw [← map_defectTwo, map_logExp φ l (constantCoeff_defectTwo hcc)]
    have hcm : ∀ G : MvPowerSeries (V2 d) F,
        MvPowerSeries.constantCoeff (MvPowerSeries.map φ G) = φ (MvPowerSeries.constantCoeff G) := by
      intro G
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    refine ⟨fun n => ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [MvPowerSeries.coeff_map]
      exact Subfield.mem_map.mpr ⟨_, h1 n, rfl⟩
    · have ht : ∀ s : ZMod d, MvPowerSeries.constantCoeff (torus l ζ s) = 0 := fun s => cc_torus l ζ s
      have := congrArg (MvPowerSeries.map φ) h2
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht)] at this
      simpa only [map_torus] using this
    · intro n hn
      rw [MvPowerSeries.coeff_map] at hn
      exact h3 n (fun h0 => hn (by rw [h0, map_zero]))
    · rw [E1]
      exact integral_map φ hφ h4
    · rw [E1, hcm, h5, map_one]
    · rw [E2]
      exact integral_map φ hφ h6
    · rw [E2, hcm, h7, map_one]
  · intro g hg hgs
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg y, map_zero]
    · have := congrArg (MvPowerSeries.map φ) (hgs y)
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_entLog,
        MvPowerSeries.map_X] at this
      exact this
end Formalism.DworkPowerSeriesWeights
