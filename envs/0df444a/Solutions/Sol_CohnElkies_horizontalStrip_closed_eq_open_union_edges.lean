-- Prove2me | solution 1 for CohnElkies.horizontalStrip_closed_eq_open_union_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/b59f516d-ecdc-48b2-b1be-9147367e6b0a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {a b : ℝ} (hab : a < b) :
    (Complex.im ⁻¹' Icc a b) =
      ((Complex.im ⁻¹' Ioo a b) ∪
        (Complex.im ⁻¹' {a})) ∪
        (Complex.im ⁻¹' {b}) := by
  ext z
  change
    (a ≤ z.im ∧ z.im ≤ b) ↔
      (((a < z.im ∧ z.im < b) ∨ z.im = a) ∨
        z.im = b)
  constructor
  · intro hz
    by_cases hbottom : z.im = a
    · exact Or.inl (Or.inr hbottom)
    by_cases htop : z.im = b
    · exact Or.inr htop
    exact Or.inl (Or.inl
      ⟨lt_of_le_of_ne hz.1 (Ne.symm hbottom),
        lt_of_le_of_ne hz.2 htop⟩)
  · intro hz
    rcases hz with (hinterior | hbottom) | htop
    · exact ⟨hinterior.1.le, hinterior.2.le⟩
    · rw [hbottom]
      exact ⟨le_rfl, hab.le⟩
    · rw [htop]
      exact ⟨hab.le, le_rfl⟩
end CohnElkies
