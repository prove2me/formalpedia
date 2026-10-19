-- Prove2me | solution 2 for CohnElkies.horizontalStrip_closed_eq_open_union_edges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:09.454675+00:00
-- url     : https://prove2.me/submissions/43665f25-e3a6-4f62-9d27-a7da64865b47

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


theorem solution
    {a b : ℝ} (hab : a < b) :
    (Complex.im ⁻¹' Icc a b) =
      ((Complex.im ⁻¹' Ioo a b) ∪
        (Complex.im ⁻¹' {a})) ∪
        (Complex.im ⁻¹' {b}) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr h2
    · exact Or.inl (Or.inr h1.symm)
  · rintro ((⟨h1, h2⟩ | h) | h)
    · exact ⟨h1.le, h2.le⟩
    · subst h; exact ⟨le_rfl, hab.le⟩
    · subst h; exact ⟨hab.le, le_rfl⟩

