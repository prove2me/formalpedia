-- Prove2me | solution 1 for Ehrhart.JetAsymptotics.normalized_jetLayercake_value_at_bodyScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/95b3b618-0891-440c-9233-d8bc0e1ecb9c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology
namespace Ehrhart.JetAsymptotics
theorem _root_.solution {n : ℕ}
    (K : CenteredBody n) {c : ℝ}
    (hscale : c ^ n = (n.factorial : ℝ) *
      normalizedVolume K.carrier) :
    c - c ^ (n + 1) /
      (((n + 1).factorial : ℝ) *
        normalizedVolume K.carrier) =
      (n : ℝ) * c / ((n : ℝ) + 1) := by
  have hvolume : normalizedVolume K.carrier ≠ 0 :=
    K.volume_pos.ne'
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsucc : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [pow_succ, hscale, Nat.factorial_succ]
  push_cast
  field_simp
  ring
end Ehrhart.JetAsymptotics
