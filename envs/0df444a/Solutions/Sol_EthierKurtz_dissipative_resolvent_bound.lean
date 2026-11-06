-- Prove2me | solution 1 for EthierKurtz.dissipative_resolvent_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:52:51.005359+00:00
-- url     : https://prove2.me/submissions/7e07bc83-ae7d-41e5-87b3-5544d5ec6f06

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.Defs.Basic
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open EthierKurtz

theorem solution {E : Type*} (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)) (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖) (fg : UniformBoundedFunction E × UniformBoundedFunction E) (hfg : fg ∈ A) {a : ℝ} (ha : 0 < a) : ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖ / a := by
  have h := hdiss fg hfg a ha
  rw [mul_comm a ‖fg.1‖] at h
  exact (le_div_iff₀ ha).mpr h
