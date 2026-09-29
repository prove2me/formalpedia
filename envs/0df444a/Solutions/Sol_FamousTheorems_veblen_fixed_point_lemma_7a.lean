-- Prove2me | solution 1 for FamousTheorems.veblen_fixed_point_lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:57:09.78042+00:00
-- url     : https://prove2.me/submissions/8996cccd-3ef5-4106-ba42-c0798667a7d3

import Mathlib

universe u

theorem solution {f : Ordinal.{u} → Ordinal.{u}} (hf : Order.IsNormal f) (a : Ordinal.{u}) : ∃ b, a ≤ b ∧ f b = b :=
  ⟨Ordinal.nfp f a, Ordinal.le_nfp f a, Ordinal.nfp_fp hf a⟩
