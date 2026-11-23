-- Prove2me | solution 1 for Bl.general_b_fact_second_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:55.607819+00:00
-- url     : https://prove2.me/submissions/64fa12a6-ab05-4fd2-a5b8-94fc4fcdee84

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_form
namespace Bl.general_b_fact_second_form
theorem _root_.solution :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [StarRing.{0} K] [inst_3 : AddCommGroup.{0} V]
  [inst_4 : Module.{0, 0} K V] [inst_5 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [inst_6 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  {Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V},
  Submodule.IsLattice.{0, 0, 0} K Λ →
    ∀ (v : V),
      Exists.{1} fun (r : NumberField.RingOfIntegers.{0} K) ↦
        And (Ne.{1} r 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} r v)) := by
  intro K V _ _ _ _ _ _ _ Λ hΛ v
  have hv : v ∈ Submodule.span K (Λ : Set V) := by
    rw [hΛ.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have h1 : (r * s) • x ∈ Λ := by rw [mul_comm, mul_smul]; exact Λ.smul_mem s hrx
    have h2 : (r * s) • y ∈ Λ := by rw [mul_smul]; exact Λ.smul_mem r hsy
    rw [smul_add]; exact Λ.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    dsimp only at hab
    refine ⟨r * (b : NumberField.RingOfIntegers K),
      mul_ne_zero hr (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have hb : (b : NumberField.RingOfIntegers K) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : NumberField.RingOfIntegers K) (c • x), smul_smul, mul_comm,
        hab, algebraMap_smul]
    rw [mul_smul, hb, smul_smul, mul_comm, ← smul_smul]
    exact Λ.smul_mem a hrx
end Bl.general_b_fact_second_form
