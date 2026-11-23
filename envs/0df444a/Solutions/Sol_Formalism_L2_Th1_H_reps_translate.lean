-- Prove2me | solution 1 for Formalism.L2.Th1.H.reps_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:50.647848+00:00
-- url     : https://prove2.me/submissions/6b64fc6d-7925-4a6c-b2f8-cee55d47efa7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} [DecidableEq V] (hS : IsReps Λ₁ Λ₂ S)
    {y : V} (hy : y ∈ Λ₂) : IsReps Λ₁ Λ₂ (S.image (fun x => y + x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    exact Λ₂.add_mem hy (hS.1 a ha)
  · intro x hx x' hx' hxx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx'
    have hab : a - b ∈ Λ₁ := by
      have e : (y + a) - (y + b) = a - b := by abel
      have hxx' : (y + a) - (y + b) ∈ Λ₁ := hxx
      rw [e] at hxx'
      exact hxx'
    exact congrArg (fun t => y + t) (hS.2.1 a ha b hb hab)
  · intro w hw
    obtain ⟨a, ha, hwa⟩ := hS.2.2 (w - y) (Λ₂.sub_mem hw hy)
    refine ⟨y + a, Finset.mem_image.2 ⟨a, ha, rfl⟩, ?_⟩
    have e : w - (y + a) = w - y - a := by abel
    rw [e]; exact hwa
end Formalism.L2.Th1.H
