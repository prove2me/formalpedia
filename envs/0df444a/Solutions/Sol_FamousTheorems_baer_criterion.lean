-- Prove2me | solution 1 for FamousTheorems.baer_criterion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:08:48.878632+00:00
-- url     : https://prove2.me/submissions/452e7a28-6b22-480c-b09a-f78a3a279a6d

import Mathlib

theorem solution {R Q : Type*} [Ring R] [AddCommGroup Q] [Module R Q] (h : Module.Baer R Q) :
    Module.Injective R Q :=
  h.injective
