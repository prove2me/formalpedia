-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.MMS_agent_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:37.273273+00:00
-- url     : https://prove2.me/submissions/2025b2e8-e4c1-4779-b298-46ff12c6123d

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_ElevenTwelfths_instV_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_sum
import Theorems.Thm_FairSelling_MMS_le_TPS_le_PS
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution {δ : ℝ} (hδ0 : 0 ≤ δ) :
    MMS 3 (instV 2) (instP δ) = 36 * δ := by
  refine le_antisymm ?_ ?_
  · have h := MMS_le_TPS_le_PS (instV 2) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 2 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 2) (instP δ) = 36 * δ := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 2 g)) = ∑ g, instP δ g := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_left]
        simpa [instV] using instP_nonneg hδ0 g
      rw [this, instP_sum]
      norm_num
      ring
    linarith [h.1, h.2]
  · refine le_MMS_of_outcome (by norm_num) (instV 2) (instP δ)
      (fun g => instV_nonneg 2 g) (instP_nonneg hδ0)
      ⟨Finset.univ, fun _ => ∅, fun _ => 36 * δ⟩ ?_ (36 * δ) ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show (∑ g ∈ (Finset.univ : Finset (Fin 8)), instP δ g) = 108 * δ from instP_sum δ]
      norm_num
      linarith
    · intro j; simp [util]
end FairSelling.ElevenTwelfths
