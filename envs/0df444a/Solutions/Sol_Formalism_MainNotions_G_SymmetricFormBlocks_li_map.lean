-- Prove2me | solution 1 for Formalism.MainNotions.G.SymmetricFormBlocks.li_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:32.636014+00:00
-- url     : https://prove2.me/submissions/02c4d9c4-2779-4d9b-81c5-d7c48a4fab20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial
namespace Formalism.MainNotions.G.SymmetricFormBlocks
theorem _root_.solution {k L : Type*} [Field k] [Field L] (ι : k →+* L) {σ κ : Type*} (f : κ → MvPolynomial σ k)
    (hf : LinearIndependent k f) : LinearIndependent L (fun i => MvPolynomial.map ι (f i)) := by
  classical
  letI := ι.toAlgebra
  have hs : LinearIndepOn k id (Set.range f) := (linearIndepOn_id_range_iff hf.injective).2 hf
  let b := Module.Basis.extend hs
  let B := (Algebra.TensorProduct.basis L b).map
    (MvPolynomial.algebraTensorAlgEquiv k L).toLinearEquiv
  have hB : ∀ x, B x = MvPolynomial.map ι (x : MvPolynomial σ k) := by
    intro x
    simp only [B, b, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      Module.Basis.coe_extend, AlgEquiv.toLinearEquiv_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hsub : Set.range f ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _
  have hinj : Function.Injective
      (fun i => (⟨f i, hsub (Set.mem_range_self i)⟩ : hs.extend (Set.subset_univ _))) := by
    intro i j hij
    exact hf.injective (congrArg Subtype.val hij)
  have := B.linearIndependent.comp _ hinj
  convert this using 1
  all_goals first
    | rfl
    | (funext i; simp only [Function.comp_apply, hB])
end Formalism.MainNotions.G.SymmetricFormBlocks
