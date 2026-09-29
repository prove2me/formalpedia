-- Prove2me | solution 1 for Freiman.section14_raw_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:36.583911+00:00
-- url     : https://prove2.me/submissions/e70e9b3b-b80a-4405-8158-125529c2945d

import Theorems.Thm_Freiman_section14_parameter_state
import Theorems.Thm_Freiman_section14_parent_modes
import Theorems.Thm_Freiman_section14_row_modes
import Theorems.Thm_Freiman_section14_endpoint_transfer
import Theorems.Thm_Freiman_section14_all_states_valid
import Theorems.Thm_Freiman_section14_catalog_sound
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hm : lowerMixed p) : section14RawGeometry p := by
  obtain ⟨i,hmatch,hrect⟩ := section14_parameter_state t p hs hm
  have hv := section14_all_states_valid i
  obtain ⟨b,hb,hparent⟩ := section14_parent_modes t p i hs hm hmatch hv
  obtain ⟨pl,hpl,hlabels,htarget,hcase⟩ := section14_row_modes p i hm hmatch
  have hpv : section14PlanValid section14Catalog (section14State section14Catalog (i.val+1)) pl := hv.2.2.2.2.1 pl hpl
  have hspecs := hpv.2.2.2.2.2.1
  intro sp hsp
  have hin : sp ∈ section14ExpectedSpecs pl.labels pl.targetLower := by
    rw [hlabels,htarget]
    exact hsp
  have hmap : sp ∈ (pl.specs.map Prod.snd).toFinset := by
    rw [hspecs]
    exact List.mem_toFinset.mpr hin
  obtain ⟨gs,hgs,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hmap)
  rw [← heq]
  apply section14_endpoint_transfer p i pl gs hm hmatch hv hpl hgs
  intro j hj hmode
  apply section14_catalog_sound i pl hpl b hb (section14R p) (section14S p) (section14Q p) hrect _ gs hgs j hj hmode
  intro bound hbound
  rcases List.mem_append.mp hbound with h | h
  · exact hcase bound h
  · exact hparent bound h
