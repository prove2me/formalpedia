-- Prove2me | solution 1 for Bl.general_b_fact_third_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.27173+00:00
-- url     : https://prove2.me/submissions/2556b428-78bc-460b-a847-d2ee40a952e8

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.general_b_fact_third_ter_form
private lemma aux {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [Module (NumberField.RingOfIntegers K) W]
    [IsScalarTower (NumberField.RingOfIntegers K) K W]
    (Λ : Submodule (NumberField.RingOfIntegers K) W)
    (hspan : Submodule.span K (Λ : Set W) = ⊤) (v : W) :
    ∃ s : NumberField.RingOfIntegers K, s ≠ 0 ∧ s • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set W) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact Λ.add_mem (Λ.smul_mem t hsx) (Λ.smul_mem s hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    dsimp only at hnd
    refine ⟨(d : NumberField.RingOfIntegers K) * s,
      mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    have e : ((d : NumberField.RingOfIntegers K) * s) • (a • x) = n • (s • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * s) (a • x),
        ← algebraMap_smul K s x, ← algebraMap_smul K n, smul_smul, smul_smul]
      congr 1
      rw [map_mul, ← hnd]
      ring
    rw [e]
    exact Λ.smul_mem n hsx
end Bl.general_b_fact_third_ter_form
end

set_option autoImplicit false
open Bl Bl.general_b_fact_third_ter_form
namespace Bl.general_b_fact_third_ter_form
theorem _root_.solution :
  ∀ {K W : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} W] [inst_3 : Module.{0, 0} K W]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) W]
  [inst_5 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K W]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) W) [hΛ : Submodule.IsLattice.{0, 0, 0} K Λ] (v : W),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} K) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro K W _ _ _ _ _ _ Λ hΛ v
  exact aux Λ hΛ.2 v
end Bl.general_b_fact_third_ter_form
