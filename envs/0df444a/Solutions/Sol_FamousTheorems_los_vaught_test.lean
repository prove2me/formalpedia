-- Prove2me | solution 1 for FamousTheorems.los_vaught_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:46.222253+00:00
-- url     : https://prove2.me/submissions/b1ade61d-85df-4939-a9a6-96420fde5dac

import Mathlib

universe u v w

theorem solution {L : FirstOrder.Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory) (h : κ.Categorical T)
    (h1 : Cardinal.aleph0 ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ M : FirstOrder.Language.Theory.ModelType.{u, v, max u v} T, Infinite M) : T.IsComplete :=
  Cardinal.Categorical.isComplete κ T h h1 h2 hS hT
