-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.length_baseChange_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:21.186799+00:00
-- url     : https://prove2.me/submissions/c60862d1-8db1-4839-ba40-a2636919e5fe

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct
open Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
theorem _root_.solution {O O₁ : Type} [CommRing O] [CommRing O₁] [Algebra O O₁]
    [Module.Flat O O₁] (ε : ℕ∞)
    (hs : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length O₁ (TensorProduct O O₁ S) = ε)
    (Q : Type) [AddCommGroup Q] [Module O Q] (h : IsFiniteLength O Q) :
    Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q := by
  induction h with
  | of_subsingleton =>
    rw [Module.length_eq_zero (R := O), mul_zero, Module.length_eq_zero_iff]
    refine ⟨fun x y => ?_⟩
    rw [← sub_eq_zero]
    generalize x - y = z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    | add u v hu hv => rw [hu, hv, add_zero]
  | of_simple_quotient hN ih =>
    rename_i M _ _ N hS
    have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have e2 := Module.length_eq_add_of_exact ((N.subtype).baseChange O₁) ((N.mkQ).baseChange O₁)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap (M := O₁) _ N.injective_subtype)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective O₁ N.mkQ_surjective)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact (M := O₁) (LinearMap.exact_subtype_mkQ N))
    rw [e1, e2, ih, hs _ hS, Module.length_eq_one_iff.mpr hS]
    ring
end Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
