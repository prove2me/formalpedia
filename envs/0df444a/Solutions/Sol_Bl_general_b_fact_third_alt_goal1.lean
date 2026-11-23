-- Prove2me | solution 1 for Bl.general_b_fact_third_alt.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:28.097379+00:00
-- url     : https://prove2.me/submissions/73c763e3-f50c-4d3c-90f9-bdc698e14fca

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_alt
namespace Bl.general_b_fact_third_alt
theorem _root_.solution :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {n : Nat}
  (R : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin n → K)) (x : Fin n → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} R)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} R (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ n R x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact R.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • y = d2 • (d1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • z = d1 • (d2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact R.add_mem (R.smul_mem _ h1) (R.smul_mem _ h2)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨(b : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
    have e : ((b : NumberField.RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K ((b : NumberField.RingOfIntegers K) * d), ← algebraMap_smul K a,
        ← algebraMap_smul K d, smul_smul, smul_smul]
      congr 1
      simp only at hab
      rw [map_mul, ← hab]
      ring
    rw [e]
    exact R.smul_mem _ h
end Bl.general_b_fact_third_alt
