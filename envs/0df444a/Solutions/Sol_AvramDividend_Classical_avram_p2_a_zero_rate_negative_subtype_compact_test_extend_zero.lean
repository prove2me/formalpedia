-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_negative_subtype_compact_test_extend_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:40:01.313011+00:00
-- url     : https://prove2.me/submissions/c85869a0-443f-42a8-b70c-1ef7da654d74

import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Logic.Function.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology AvramDividend.Classical

/-- Compact-supported negative-subtype tests extend by zero to real compact-negative tests. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Iio (0 : ℝ) ∧
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) := by
  let e : {x : ℝ // x < 0} → ℝ := Subtype.val
  let g : ℝ → ℝ := Function.extend e (fun x => f x) 0
  have hfcompact : HasCompactSupport (fun x : {x : ℝ // x < 0} => f x) :=
    f.hasCompactSupport
  have hfcontinuous : Continuous (fun x : {x : ℝ // x < 0} => f x) :=
    f.continuous
  have hecont : Continuous e := continuous_subtype_val
  have hgin : Continuous g :=
    HasCompactSupport.continuous_extend_zero isOpen_Iio hfcontinuous hfcompact
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.extend_zero hfcompact hecont
  have hsupport :
      tsupport g = e '' tsupport (fun x : {x : ℝ // x < 0} => f x) :=
    HasCompactSupport.tsupport_extend_zero hfcompact hecont Subtype.val_injective
  refine ⟨g, hgin, hgcompact, ?_, ?_⟩
  · rw [hsupport]
    rintro y ⟨x, hx, rfl⟩
    exact x.property
  · intro x
    exact Function.Injective.extend_apply Subtype.val_injective
      (fun x : {x : ℝ // x < 0} => f x) (fun _ => (0 : ℝ)) x
