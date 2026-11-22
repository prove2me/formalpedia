-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.centralExtAbelian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:17:01.369593+00:00
-- url     : https://prove2.me/submissions/99fcecbe-1e34-4aff-a6ab-bdbab6ec1fc9

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open scoped commutatorElement
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : CentralExtAbelian := by
  intro H G _ _ π _hsurj hker D hD hcase x y
  rcases hcase with hcomp | ⟨hDtop, hDab⟩
  ·
    have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
      intro a ha b hb
      have hmem : a * b * (b * a)⁻¹ ∈ D ⊓ π.ker := by
        refine ⟨D.mul_mem (D.mul_mem ha hb) (D.inv_mem (D.mul_mem hb ha)), ?_⟩
        refine MonoidHom.mem_ker.mpr ?_
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (π a) (π b), mul_inv_cancel]
      rw [hcomp, Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem

    have hdec : ∀ x : H, ∃ d ∈ D, ∃ z ∈ Subgroup.center H, x = d * z := by
      intro x
      have hx : π x ∈ D.map π := by rw [hD]; exact Subgroup.mem_top _
      obtain ⟨d, hdD, hdx⟩ := Subgroup.mem_map.mp hx
      refine ⟨d, hdD, d⁻¹ * x, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hdec x
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hdec y
    have c1 := Subgroup.mem_center_iff.mp hz₁
    have c2 := Subgroup.mem_center_iff.mp hz₂
    calc d₁ * z₁ * (d₂ * z₂) = d₁ * d₂ * (z₁ * z₂) := by
          rw [mul_assoc d₁ z₁, ← mul_assoc z₁ d₂, ← c1 d₂]; group
      _ = d₂ * d₁ * (z₂ * z₁) := by rw [hDcomm d₁ hd₁ d₂ hd₂, c1 z₂]
      _ = d₂ * z₂ * (d₁ * z₁) := by
          rw [mul_assoc d₂ z₂, ← mul_assoc z₂ d₁, ← c2 d₁]; group
  · exact hDab x (hDtop ▸ Subgroup.mem_top x) y (hDtop ▸ Subgroup.mem_top y)
end Formalism.TwoAdicCyclotomicDecomposition
