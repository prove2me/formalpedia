-- Prove2me | solution 1 for Bl.general_b_fact_second_alt.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:11.876485+00:00
-- url     : https://prove2.me/submissions/b2d400a4-9f93-477f-8e06-d4aaab12fe41

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_alt
namespace Bl.general_b_fact_second_alt
theorem _root_.solution :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)) (v : Fin r → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (a : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} a 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} a v)) := by
  intro K _ _ r L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨(d : NumberField.RingOfIntegers K) * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ha, ?_⟩
    have key : ((d : NumberField.RingOfIntegers K) * a) • (c • x) = n • (a • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * a), ← algebraMap_smul K a,
        ← algebraMap_smul K n, smul_smul, smul_smul]
      simp only at hnd
      rw [← hnd, map_mul]
      congr 1
      ring
    rw [key]
    exact L.smul_mem n hax
end Bl.general_b_fact_second_alt
