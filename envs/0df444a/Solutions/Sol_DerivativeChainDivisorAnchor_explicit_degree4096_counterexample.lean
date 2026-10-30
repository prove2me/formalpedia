-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.explicit_degree4096_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:20:35.613689+00:00
-- url     : https://prove2.me/submissions/e028cef4-a627-47b0-9a71-7ad80954926b

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_cost_lower
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_lower_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
import Theorems.Thm_DerivativeChainDivisorAnchor_obstruction_anchor_upper
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

theorem scaled_binomial (n : ℕ) (r : ℂ) :
    (base n).scaleRoots r = X^(n+2)-C (r^(n+2)) := by
  ext i
  rw [coeff_scaleRoots, base_degree]
  simp only [base, coeff_sub, coeff_X_pow, coeff_one, coeff_C]
  by_cases hi : i=n+2
  · subst i
    simp
  by_cases hi0 : i=0
  · subst i
    simp
  · simp [hi, hi0, eq_comm]








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






theorem orbitCount_pos (k : ℕ) (hk : 3 ≤ k) : 0 < orbitCount k := by
  unfold orbitCount
  positivity

theorem orbit_index (k : ℕ) (hk : 3 ≤ k) : orbitCount k-2+2=orbitCount k := by
  have hp : 0 < k^4 := pow_pos (by omega : 0 < k) 4
  unfold orbitCount
  omega

theorem innerRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < innerRadius k ∧ innerRadius k < 1 := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hs : (0:ℝ) < (k:ℝ)^2 := by positivity
  unfold innerRadius
  constructor
  · positivity
  · apply (div_lt_one hs).mpr
    nlinarith



theorem childRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < childRadius k ∧ childRadius k < 1 := by
  have hp := childRadiusPower_bounds k hk
  unfold childRadius
  exact ⟨Real.rpow_pos_of_pos hp.1 _, Real.rpow_lt_one hp.1.le hp.2.1
    (inv_pos.mpr (by exact_mod_cast orbitCount_pos k hk))⟩









end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section






theorem obstruction_source_formula (k : ℕ) (hk : 3 ≤ k) :
    obstructionSource k = (X^orbitCount k-C ((innerRadius k:ℂ)^orbitCount k))*
      (X^orbitCount k-1)^(k-1) := by
  unfold obstructionSource anchorSource
  rw [scaled_binomial]
  simp only [base, orbit_index k hk]



theorem obstruction_degree (k : ℕ) (hk : 3 ≤ k) :
    (obstructionSource k).natDegree = orbitCount k*k := by
  rw [obstructionSource, anchor_source_degree _ k (by omega), orbit_index k hk]





theorem obstruction_anchor_lower (k : ℕ) (hk : 3 ≤ k) : (2/3:ℝ) ≤ obstructionAnchor k := by
  exact anchor_lower_bound (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (childRadius_bounds k hk).1 (childRadius_bounds k hk).2.le



theorem obstruction_cost_lower (k : ℕ) (hk : 3 ≤ k) :
    ((orbitCount k:ℝ)-1)*innerRadius k ≤ obstructionCost k := by
  have h := anchor_cost_lower (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le (childRadius_bounds k hk).1.ne'
  have hi : ((orbitCount k-2:ℕ):ℝ)+2 = (orbitCount k:ℝ) := by exact_mod_cast orbit_index k hk
  change _ ≤ (((anchorSource (orbitCount k-2) k (innerRadius k)).natDegree:ℝ)-1)*
    uniformRootW1 (anchorSource (orbitCount k-2) k (innerRadius k)) (anchorChild (orbitCount k-2) k (childRadius k))
  have hi1 : ((orbitCount k-2:ℕ):ℝ)+1 = (orbitCount k:ℝ)-1 := by linarith
  rw [hi1] at h
  exact h














end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor



























set_option maxRecDepth 20000 in
theorem solution :
    obstructionSource 4 = (X^1024-C ((1/16:ℂ)^1024))*(X^1024-1)^3 ∧
    (obstructionSource 4).natDegree = 4096 ∧
    (2/3:ℝ) ≤ obstructionAnchor 4 ∧ obstructionAnchor 4 < 14 ∧
    (1023/16:ℝ) ≤ obstructionCost 4 ∧
    (1023/224:ℝ) < obstructionCost 4/obstructionAnchor 4 ∧
    4 < obstructionCost 4/obstructionAnchor 4 := by
  have hA := obstruction_anchor_lower 4 (by norm_num)
  have hAu := obstruction_anchor_upper 4 (by norm_num)
  have hC := obstruction_cost_lower 4 (by norm_num)
  norm_num [orbitCount, innerRadius] at hAu hC
  have hR : (1023/224:ℝ) < obstructionCost 4/obstructionAnchor 4 := by
    apply (lt_div_iff₀ (by linarith : 0 < obstructionAnchor 4)).mpr
    nlinarith
  refine ⟨?_, ?_, hA, hAu, hC, hR, by linarith⟩
  · have hs := obstruction_source_formula 4 (by norm_num)
    rw [show orbitCount 4=1024 by norm_num [orbitCount],
      show (innerRadius 4:ℂ)=(1/16:ℂ) by norm_num [innerRadius]] at hs
    exact hs
  · norm_num [obstruction_degree 4 (by norm_num), orbitCount]
