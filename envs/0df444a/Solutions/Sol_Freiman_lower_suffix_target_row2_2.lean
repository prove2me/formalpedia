-- Prove2me | solution 2 for Freiman.lower_suffix_target_row2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:59:40.342399+00:00
-- url     : https://prove2.me/submissions/1d3dc519-a525-4fde-957d-8652b6f6039f

import Theorems.Thm_Freiman_lowerHistory_row2_catalog_partition
import Theorems.Thm_Freiman_lowerHistory_catalog_descriptor
import Theorems.Thm_Freiman_lowerHistory_catalog_shapes
import Theorems.Thm_Freiman_lowerHistory_source_events
import Theorems.Thm_Freiman_lowerHistory_reached_rectangle
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lowerHistory_survivor_target
import Theorems.Thm_Freiman_lowerHistory_comparison_transfer
import Theorems.Thm_Freiman_lowerHistory_greater_semantics
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_earlier_anchor
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_01
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_02
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_03
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_04
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_05
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_06
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_07
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_08
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_09
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_10
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_11
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_12
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_13
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_14
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_15
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_16
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_17
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_18
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_19
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_20
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_21
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_22
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_23
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_24
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_25
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_26
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_27
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_28
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_29
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_30
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_32
import Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_33
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → lowerRStar (h n) →
    lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  intro hm ha hR
  have haz : lowerHistoryHazard 2 (h n) := ⟨hm,ha,hR⟩
  obtain ⟨base,p,hmem,hreach,hrow⟩ :=
    lowerHistory_catalog_descriptor t h n 2 hh (by decide) haz
  have hp := lowerHistory_catalog_shapes p hmem
  have hazp : lowerHistoryHazard p.row (h n) := by simpa only [hrow] using haz
  have he := lowerHistory_source_events t h n hh base p hp hreach hazp
  have hr := lowerHistory_reached_rectangle lower_entry_family_domain t h n hh
    base p hmem hp hreach
  have ht : lowerHistoryTarget p.row (h n) t := by
    rcases lowerHistory_row2_catalog_partition p hmem hrow with
      hsurv | hc1 | hc2 | hc3 | hc4 | hc5 | hc6 | hc7 | hc8 | hc9 | hc10 | hc11 | hc12 | hc13 | hc14 | hc15 | hc16 | hc17 | hc18 | hc19 | hc20 | hc21 | hc22 | hc23 | hc24 | hc25 | hc26 | hc27 | hc28 | hc29 | hc30 | hc32 | hc33
    · exact lowerHistory_survivor_target t h n hh base p hp hreach hsurv
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_01 base p hc1 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_02 base p hc2 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_03 base p hc3 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_04 base p hc4 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_05 base p hc5 he hr)
    · obtain ⟨hi,h4,hc⟩ := Freiman.lowerHistory_row2_certificate_case_06 base p hc6 he hr
      exact lowerHistory_comparison_transfer lowerHistory_greater_semantics
        lowerHistory_endpoint_semantics t h n hh base p hp hreach hi h4
        (lowerHistory_earlier_anchor t h n hh base p hp hreach hi) hc
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_07 base p hc7 he hr)
    · obtain ⟨hi,h4,hc⟩ := Freiman.lowerHistory_row2_certificate_case_08 base p hc8 he hr
      exact lowerHistory_comparison_transfer lowerHistory_greater_semantics
        lowerHistory_endpoint_semantics t h n hh base p hp hreach hi h4
        (lowerHistory_earlier_anchor t h n hh base p hp hreach hi) hc
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_09 base p hc9 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_10 base p hc10 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_11 base p hc11 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_12 base p hc12 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_13 base p hc13 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_14 base p hc14 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_15 base p hc15 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_16 base p hc16 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_17 base p hc17 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_18 base p hc18 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_19 base p hc19 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_20 base p hc20 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_21 base p hc21 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_22 base p hc22 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_23 base p hc23 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_24 base p hc24 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_25 base p hc25 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_26 base p hc26 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_27 base p hc27 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_28 base p hc28 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_29 base p hc29 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_30 base p hc30 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_32 base p hc32 he hr)
    · exact False.elim (Freiman.lowerHistory_row2_certificate_case_33 base p hc33 he hr)
  simpa only [hrow,lowerHistoryTarget] using ht
#print axioms solution
