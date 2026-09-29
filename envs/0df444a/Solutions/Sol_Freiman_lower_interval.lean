-- Prove2me | solution 1 for Freiman.lower_interval
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:34.601845+00:00
-- url     : https://prove2.me/submissions/960abdcc-0708-48b1-8ced-b2b0d5287718

import Theorems.Thm_Freiman_lower_models
import Theorems.Thm_Freiman_lower_model_realization
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution : Set.Icc cF (Real.sqrt 21) ⊆ lagrangeSpectrum := by
  intro t ht
  exact lower_model_realization t ht.1 (lower_models t ht)
