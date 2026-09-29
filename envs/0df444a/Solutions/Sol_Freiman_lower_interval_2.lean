-- Prove2me | solution 2 for Freiman.lower_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T21:49:56.962235+00:00
-- url     : https://prove2.me/submissions/1d8a77bb-dc7c-4fb7-ac47-ea043a94d796

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_cF
import Theorems.Thm_Freiman_lower_models
import Theorems.Thm_Freiman_lower_model_realization

open Freiman

theorem solution :
    Set.Icc cF (Real.sqrt 21) ⊆ lagrangeSpectrum := by
  intro t ht
  exact lower_model_realization t ht.1 (lower_models t ht)
