-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:04.652359+00:00
-- url     : https://prove2.me/submissions/46255911-36fc-4a82-baf6-dfb9d1d3e7b4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
private theorem exists_subring_iff_ge_zero : ∃ R : Subring C, ∀ a, a ∈ R ↔ V.Ge 0 a := by
  refine ⟨{ carrier := {a | V.Ge 0 a}
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, fun a => Iff.rfl⟩
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
    rw [AddValuation.map_mul]
    rw [WithTop.coe_zero] at ha' hb' ⊢
    exact add_nonneg ha' hb'
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
    rw [AddValuation.map_one, WithTop.coe_zero]
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a + b)
    exact le_trans (le_min ha' hb') (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top
  · intro a ha
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (-a)
    rw [AddValuation.map_neg]
    exact ha'
namespace Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
end Cart
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
end Sys
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds
namespace VF.Ge
theorem _root_.solution {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  exact (hR _).1 (prod_mem fun i hi => (hR _).2 (h i hi))
end VF.Ge
end Formalism.L2.FormalSeriesBounds
