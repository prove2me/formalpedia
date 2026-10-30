-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.explicit_pair_drop_k5
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:35:36.823772+00:00
-- url     : https://prove2.me/submissions/85bcb721-7c6f-4bec-8297-39db431d7bfa

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_PairDropNoGo
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
import Theorems.Thm_DerivativeChainDivisorAnchor_pair_ratio_bound
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section






theorem base_monic (n : ℕ) : (base n).Monic := by
  simpa [base] using monic_X_pow_sub_C (R := ℂ) 1 (n := n+2) (by omega)





























end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section










theorem anchor_source_degree (n k : ℕ) (hk : 1 ≤ k) (a : ℝ) :
    (anchorSource n k a).natDegree = (n+2)*k := by
  rw [anchorSource, natDegree_mul ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero
    (pow_ne_zero _ (base_monic n).ne_zero), natDegree_scaleRoots, natDegree_pow, base_degree]
  calc
    _ = (n+2)*((k-1)+1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hk]









end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainDivisorAnchor
noncomputable section








theorem orbit_index (k : ℕ) (hk : 3 ≤ k) : orbitCount k-2+2=orbitCount k := by
  have hp : 0 < k^4 := pow_pos (by omega : 0 < k) 4
  unfold orbitCount
  omega















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section










theorem obstruction_degree (k : ℕ) (hk : 3 ≤ k) :
    (obstructionSource k).natDegree = orbitCount k*k := by
  rw [obstructionSource, anchor_source_degree _ k (by omega), orbit_index k hk]
























end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section









theorem power_source_degree (P : ℂ[X]) (r : ℕ) : (powerSource P r).natDegree = r*P.natDegree := by
  simp only [powerSource, natDegree_pow, mul_comm]





















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section













theorem pair_degree_factor (k : ℕ) (hk : 3 ≤ k) :
    (pairSource k).natDegree = 12*(orbitCount k)^2*k := by
  rw [pairSource, power_source_degree, obstruction_degree k hk]
  unfold powerMultiplicity
  ring

theorem pair_degree (k : ℕ) (hk : 3 ≤ k) : (pairSource k).natDegree = 192*k^9 := by
  rw [pair_degree_factor k hk]
  unfold orbitCount
  ring























end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor






































theorem solution :
    (pairSource 5).natDegree=375000000 ∧ (25/6:ℝ) < pairRatio 5 ∧ 4 < pairRatio 5 := by
  have h := (pair_ratio_bound 5 (by norm_num)).2
  norm_num at h
  exact ⟨by norm_num [pair_degree 5 (by norm_num)], h, by linarith⟩
