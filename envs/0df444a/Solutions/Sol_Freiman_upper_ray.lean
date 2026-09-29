-- Prove2me | solution 1 for Freiman.upper_ray
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:18.39379+00:00
-- url     : https://prove2.me/submissions/e7d245e1-d952-4cf8-ae79-44bb36f07856

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_symbolic_realization
import Theorems.Thm_Freiman_lagrange_symbolic

open Freiman

theorem solution : Set.Ici upperRayStart ⊆ lagrangeSpectrum := by
  intro t ht
  rw [lagrange_symbolic]
  exact upper_symbolic_realization t ht
