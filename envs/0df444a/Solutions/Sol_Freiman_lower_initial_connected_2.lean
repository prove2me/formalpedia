-- Prove2me | solution 2 for Freiman.lower_initial_connected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:34:57.271667+00:00
-- url     : https://prove2.me/submissions/a571ca09-ebdb-43fa-af8a-27cd77c14523

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_gluing
import Theorems.Thm_Freiman_lower_initial_seams
import Theorems.Thm_Freiman_lower_initial_limits
import Theorems.Thm_Freiman_lower_fixed_union_connected
import Theorems.Thm_Freiman_lower_fixed_family_overlap

open Freiman

open scoped BigOperators

-- `lower_initial_gluing` is the gluing lemma: given the seam package, the limit package,
-- connectedness of the fixed-root union, and the family overlap, `lowerInitialSet` is
-- preconnected. Each of the four inputs is an existing node, so connectedness follows by
-- one application.
theorem solution : IsPreconnected lowerInitialSet :=
  lower_initial_gluing lower_initial_seams lower_initial_limits
    lower_fixed_union_connected lower_fixed_family_overlap
