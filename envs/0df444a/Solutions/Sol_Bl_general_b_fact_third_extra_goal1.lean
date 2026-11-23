-- Prove2me | solution 1 for Bl.general_b_fact_third_extra.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:09.689304+00:00
-- url     : https://prove2.me/submissions/801dcd10-4138-4988-b728-8b473e728c65

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Lemmata_GeneralBFactThirdExtra_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_extra
namespace Bl.general_b_fact_third_extra
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (v : S.V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro E _ _ _ S Λ hspan v
  have hv : v ∈ Submodule.span E (SetLike.coe Λ) := by
    rw [hspan]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • x = d₂ • (d₁ • x) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • y = d₁ • (d₂ • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ h₁) (Λ.smul_mem _ h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) a
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hm' : algebraMap (NumberField.RingOfIntegers E) E m ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
    have key : (m * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul E (m * d), ← algebraMap_smul E n, ← algebraMap_smul E d,
        smul_smul, smul_smul, ← hnm]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact Λ.smul_mem n h
end Bl.general_b_fact_third_extra
