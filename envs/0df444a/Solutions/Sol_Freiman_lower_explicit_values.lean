-- Prove2me | solution 1 for Freiman.lower_explicit_values
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:06.649986+00:00
-- url     : https://prove2.me/submissions/7116d30a-31e7-4e41-b97a-0c7cdaf8ee87

import Theorems.Thm_Freiman_lower_cF_model
import Theorems.Thm_Freiman_lower_run_limit_model
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (ht : lowerExplicitValue t) : lowerHasValue t := by
  rcases ht with rfl | ⟨f,n,k,hf,rfl⟩
  · exact ⟨lowerCFSequence, lower_cF_model⟩
  · exact ⟨lowerPeriodicSequence (lowerFamilyLimitPair f n k) [3], lower_run_limit_model f n k hf, rfl⟩
