-- Prove2me | solution 1 for Bl.general_b_fact_third_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:14.557179+00:00
-- url     : https://prove2.me/submissions/6915742c-0947-448c-8445-1f76c6429b9d

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_form
namespace Bl.general_b_fact_third_form
theorem _root_.solution :
  ∀ {E V : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E] [inst_3 : AddCommGroup.{0} V]
  [inst_4 : Module.{0, 0} E V] [FiniteDimensional.{0, 0} E V]
  [inst_6 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [inst_7 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V) [hΛ : Submodule.IsLattice.{0, 0, 0} E Λ] (v : V),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} E) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro E V _ _ _ _ _ _ _ _ Λ hΛ v
  have hv : v ∈ Submodule.span E (Λ : Set V) := by
    rw [hΛ.span_eq_top]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Λ.smul_mem t hsx
    · rw [mul_smul]
      exact Λ.smul_mem s hty
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨p, hp⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    have key : ((p.2 : NumberField.RingOfIntegers E)) • (a • x) = p.1 • x := by
      rw [← algebraMap_smul E (p.2 : NumberField.RingOfIntegers E) (a • x), smul_smul, mul_comm, hp,
        algebraMap_smul]
    refine ⟨s * (p.2 : NumberField.RingOfIntegers E), mul_ne_zero hs (nonZeroDivisors.ne_zero p.2.2), ?_⟩
    rw [mul_smul, key, ← mul_smul, mul_comm, mul_smul]
    exact Λ.smul_mem p.1 hsx
end Bl.general_b_fact_third_form
