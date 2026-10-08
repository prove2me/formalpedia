-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.gammaFun_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:56.829219+00:00
-- url     : https://prove2.me/submissions/7d6443f5-a6e2-426c-8ca0-ca003b6a326e

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- `γ(I,J) = 0` iff `T[I,J]` is the zero matrix. -/
theorem pk_gammaFun_eq_zero_iff {R C F : Type*} [Zero F] (T : Matrix R C F) (I : Finset R)
    (J : Finset C) :
    GammaFun T I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, T i j = 0 := by
  classical
  unfold GammaFun
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i hi j hj
    by_contra hne
    exact h i (Finset.mem_filter.2 ⟨hi, j, hj, hne⟩)
  · intro h i hi
    obtain ⟨hiI, j, hj, hne⟩ := Finset.mem_filter.1 hi
    exact hne (h i hiI j hj)

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C F : Type*} [Zero F] (T : Matrix R C F) (I : Finset R)
    (J : Finset C) :
    GammaFun T I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, T i j = 0 :=
  pk_gammaFun_eq_zero_iff T I J

#print axioms solution
