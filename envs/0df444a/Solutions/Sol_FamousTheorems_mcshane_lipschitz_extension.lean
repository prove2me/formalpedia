-- Prove2me | solution 1 for FamousTheorems.mcshane_lipschitz_extension
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:43.802455+00:00
-- url     : https://prove2.me/submissions/be0cb755-b973-4f3f-9f43-6fa18eb97b7d

import Mathlib

theorem solution {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {s : Set α} {K : NNReal} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ Set.EqOn f g s :=
  hf.extend_real
