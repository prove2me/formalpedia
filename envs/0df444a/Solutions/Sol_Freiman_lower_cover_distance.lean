-- Prove2me | solution 1 for Freiman.lower_cover_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:20.470492+00:00
-- url     : https://prove2.me/submissions/d5c8cefe-86c1-4d63-992f-24573835aad4

import Theorems.Thm_Freiman_lower_endpoint_distance
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) (hp : lowerAdmissible p) (a : ℤ → ℕ+)
    (ha : LowerModel a) (hc : lowerCylinder p a) (t : ℝ) (ht : t ∈ lowerCover p) :
    |localValue a 0 - t| ≤ lowerCylinderError p := by
  have h₁ := lower_endpoint_distance p hp a ha hc false
  have h₂ := lower_endpoint_distance p hp a ha hc true
  rw [abs_le] at h₁ h₂ ⊢
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
