-- Prove2me | solution 1 for Bl.general_b_fact_second.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:17.703393+00:00
-- url     : https://prove2.me/submissions/1c466bc6-fc87-4061-8bf0-9c7ed29b7cbe

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second
namespace Bl.general_b_fact_second
theorem _root_.solution :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)),
  Eq.{1} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (x : Fin r → K),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ r L hL x
  have hx : x ∈ Submodule.span K (L : Set (Fin r → K)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem d2 h1
    · rw [mul_smul]; exact L.smul_mem d1 h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(c : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero c) hd, ?_⟩
    have e : ((c : NumberField.RingOfIntegers K) * d) • (a • y) = b • (d • y) := by
      calc ((c : NumberField.RingOfIntegers K) * d) • (a • y)
          = (c : NumberField.RingOfIntegers K) • (a • (d • y)) := by rw [mul_smul, smul_comm d a y]
        _ = (algebraMap (NumberField.RingOfIntegers K) K c) • (a • (d • y)) := (algebraMap_smul K _ _).symm
        _ = (a * algebraMap (NumberField.RingOfIntegers K) K c) • (d • y) := by rw [smul_smul, mul_comm]
        _ = b • (d • y) := by rw [hbc, algebraMap_smul]
    rw [e]
    exact L.smul_mem b h
end Bl.general_b_fact_second
