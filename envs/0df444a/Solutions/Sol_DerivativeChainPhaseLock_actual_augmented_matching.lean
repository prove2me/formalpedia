-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_augmented_matching
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:21:38.194849+00:00
-- url     : https://prove2.me/submissions/27b94d11-6412-4bdb-8f0c-f06a64dc777a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPhaseLock_uniform_augmented_matching
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Matrix DerivativeChainContinuation
open DerivativeChainPhaseLock






theorem solution (n : ℕ) (a : Fin (n+2) → ℂ) :
    ∃ b : Fin (n+1) → ℂ,
      (_root_.DerivativeChainPrivate.fromRoots a).derivative=
        C (n+2:ℂ)*_root_.DerivativeChainPrivate.fromRoots b ∧
      _root_.DerivativeChainContinuation.complexCentroid b=_root_.DerivativeChainContinuation.complexCentroid a ∧
      ∃ σ : Equiv.Perm (Fin (n+2)),
        (∑ i,‖a (σ i)-(Fin.snoc b (_root_.DerivativeChainContinuation.complexCentroid a) : Fin (n+2) → ℂ) i‖^2) ≤
          (∑ j,‖a j-_root_.DerivativeChainContinuation.complexCentroid a‖^2)-(∑ i,‖b i-_root_.DerivativeChainContinuation.complexCentroid a‖^2) := by
  obtain ⟨r,htop,hs⟩ := _root_.DerivativeChainContinuation.uniform_polynomial_tower (n+1) a
  have hstep := hs n (by omega)
  refine ⟨r n,?_,?_,?_⟩
  · simpa only [_root_.DerivativeChainContinuation.complexRowProduct,htop,_root_.DerivativeChainPrivate.fromRoots] using hstep.1
  · simpa only [htop] using (_root_.DerivativeChainPrefixLaws.uniform_step_centroid r n hstep).symm
  · simpa only [htop] using _root_.DerivativeChainPhaseLock.uniform_augmented_matching r n hstep
