-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickOrbit.part_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:05.409812+00:00
-- url     : https://prove2.me/submissions/2bc932a4-052f-4f86-a1c6-c6b42a7e2c3d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.ThickOrbit
namespace Formalism.FrobeniusOrbits.ThickOrbit
theorem _root_.solution {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2 := by
  set S := (Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h)) with hS
  by_contra hlt
  push_neg at hlt
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a := S.min' hne
  set c := S.max' hne
  have hcard : 0 < ((S.erase c).erase a).card := by
    have h1 := Finset.pred_card_le_card_erase (s := S) (a := c)
    have h2 := Finset.pred_card_le_card_erase (s := S.erase c) (a := a)
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbS' : b ∈ S.erase c := Finset.mem_of_mem_erase hb
  have hbc : b ≠ c := Finset.ne_of_mem_erase hbS'
  have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
  have haS : a ∈ S := S.min'_mem hne
  have hcS : c ∈ S := S.max'_mem hne
  have hab : a < b := lt_of_le_of_ne (S.min'_le b hbS) (Ne.symm hba)
  have hbc' : b < c := lt_of_le_of_ne (S.le_max' b hbS) hbc
  rw [hS, Finset.mem_filter] at haS hbS hcS
  exact key T hT hR u₀ t h hord i₀ a b c haS.1 hcS.1 hab hbc' haS.2 hbS.2 hcS.2
end Formalism.FrobeniusOrbits.ThickOrbit
