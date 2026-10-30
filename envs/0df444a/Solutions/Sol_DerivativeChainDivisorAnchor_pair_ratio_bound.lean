-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.pair_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:29:28.775556+00:00
-- url     : https://prove2.me/submissions/9e03f188-e25e-4124-9534-e93df245434d

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_PairDropNoGo
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
import Definitions.Def_DerivativeChainGini_PairDropSignedEnergy
import Theorems.Thm_DerivativeChainDivisorAnchor_actual_divisor_energy_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_lower_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
import Theorems.Thm_DerivativeChainDivisorAnchor_obstruction_anchor_upper
import Theorems.Thm_DerivativeChainDivisorAnchor_power_pair_drop
import Theorems.Thm_DerivativeChainDivisorAnchor_powered_obstruction_cost_lower
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






theorem anchor_source_monic (n k : ℕ) (a : ℝ) : (anchorSource n k a).Monic := by
  exact ((monic_scaleRoots_iff _).mpr (base_monic n)).mul ((base_monic n).pow _)

theorem anchor_child_monic (n k : ℕ) (b : ℝ) : (anchorChild n k b).Monic := by
  exact ((monic_X_pow _).mul ((base_monic n).pow _)).mul ((monic_scaleRoots_iff _).mpr (base_monic n))

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







theorem parameter_cost_gap (k : ℕ) (hk : 3 ≤ k) :
    (k:ℝ)*(3*(k:ℝ)+2) < ((orbitCount k : ℝ)-1)*innerRadius k := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hs : (3:ℝ) ≤ (k:ℝ)^2-2*(k:ℝ) := by nlinarith [sq_nonneg ((k:ℝ)-3)]
  have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (k:ℝ))
  have hgap : (0:ℝ) < (k:ℝ)^4-2*(k:ℝ)^3-1 := by nlinarith
  unfold orbitCount innerRadius
  push_cast
  rw [← mul_div_assoc, mul_one]
  apply (lt_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2)).mpr
  nlinarith

end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section








theorem obstruction_source_monic (k : ℕ) : (obstructionSource k).Monic :=
  anchor_source_monic _ _ _

theorem obstruction_degree (k : ℕ) (hk : 3 ≤ k) :
    (obstructionSource k).natDegree = orbitCount k*k := by
  rw [obstructionSource, anchor_source_degree _ k (by omega), orbit_index k hk]





theorem obstruction_anchor_lower (k : ℕ) (hk : 3 ≤ k) : (2/3:ℝ) ≤ obstructionAnchor k := by
  exact anchor_lower_bound (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (childRadius_bounds k hk).1 (childRadius_bounds k hk).2.le


















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







theorem powerMultiplicity_pos (k : ℕ) (hk : 3 ≤ k) : 1 ≤ powerMultiplicity k := by
  have hq := orbitCount_pos k hk
  unfold powerMultiplicity
  omega





theorem pair_degree_factor (k : ℕ) (hk : 3 ≤ k) :
    (pairSource k).natDegree = 12*(orbitCount k)^2*k := by
  rw [pairSource, power_source_degree, obstruction_degree k hk]
  unfold powerMultiplicity
  ring









theorem pair_drop_identity (k : ℕ) (hk : 3 ≤ k) :
    pairDrop (pairSource k) (pairChild k) =
      (pairSource k).natDegree*obstructionAnchor k+divisorEnergy (obstructionSource k) (obstructionChild k) := by
  have hn : 0 < (obstructionSource k).natDegree := by
    rw [obstruction_degree k hk]
    exact Nat.mul_pos (orbitCount_pos k hk) (by omega)
  have h := power_pair_drop (obstructionSource k) (obstructionChild k) (obstruction_source_monic k)
    (anchor_child_monic _ _ _) hn (powerMultiplicity k) (powerMultiplicity_pos k hk)
  simpa only [pairSource, pairChild, obstructionAnchor, power_source_degree, Nat.cast_mul] using h

theorem obstruction_energy_bound (k : ℕ) (hk : 3 ≤ k) :
    |divisorEnergy (obstructionSource k) (obstructionChild k)| < 8*(orbitCount k:ℝ)^2 := by
  have h := actual_divisor_energy_bound (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le (childRadius_bounds k hk).1 (childRadius_bounds k hk).2.le
  have hi : ((orbitCount k-2:ℕ):ℝ)+2=(orbitCount k:ℝ) := by exact_mod_cast orbit_index k hk
  rw [hi] at h
  exact h

theorem pair_cost_lower (k : ℕ) (hk : 3 ≤ k) :
    ((orbitCount k:ℝ)-1)*innerRadius k ≤ poweredCost k :=
  powered_obstruction_cost_lower k (powerMultiplicity k) hk (powerMultiplicity_pos k hk)











end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor






























theorem solution (k : ℕ) (hk : 3 ≤ k) :
    0 < pairDrop (pairSource k) (pairChild k) ∧ (k:ℝ)^2/((k:ℝ)+1) < pairRatio k := by
  let N : ℝ := (pairSource k).natDegree
  let A : ℝ := obstructionAnchor k
  let E : ℝ := divisorEnergy (obstructionSource k) (obstructionChild k)
  let M : ℝ := N*A
  let H : ℝ := 8*(orbitCount k:ℝ)^2
  let D : ℝ := pairDrop (pairSource k) (pairChild k)
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hq0 : (0:ℝ) < orbitCount k := by exact_mod_cast orbitCount_pos k hk
  have hH : 0 < H := by dsimp [H]; positivity
  have hN : N=12*(orbitCount k:ℝ)^2*(k:ℝ) := by
    dsimp [N]
    rw [pair_degree_factor k hk]
    push_cast
    ring
  have hN0 : 0 < N := by rw [hN]; positivity
  have hA : (2/3:ℝ) ≤ A := obstruction_anchor_lower k hk
  have hM : H*(k:ℝ) ≤ M := by
    have h := mul_le_mul_of_nonneg_left hA hN0.le
    dsimp [M, H]
    rw [hN] at h ⊢
    nlinarith
  have hE := abs_lt.mp (obstruction_energy_bound k hk)
  change -H < E ∧ E < H at hE
  have hD : D=M+E := pair_drop_identity k hk
  have hD0 : 0 < D := by
    have ht := mul_le_mul_of_nonneg_left hk3 hH.le
    nlinarith [hE.1]
  have hED := mul_lt_mul_of_pos_left hE.2 hk0
  have hkD : (k:ℝ)*D < ((k:ℝ)+1)*M := by
    rw [hD]
    nlinarith
  have hAu := obstruction_anchor_upper k hk
  have hCl := pair_cost_lower k hk
  have hgap := parameter_cost_gap k hk
  have hAC : (k:ℝ)*A < poweredCost k := by
    have h := mul_lt_mul_of_pos_left hAu hk0
    nlinarith
  have hnum := mul_lt_mul_of_pos_left hAC hN0
  have h1 := mul_lt_mul_of_pos_left hkD hk0
  have h2 := mul_lt_mul_of_pos_right hnum (by linarith : (0:ℝ) < (k:ℝ)+1)
  refine ⟨hD0, ?_⟩
  change (k:ℝ)^2/((k:ℝ)+1) < N*poweredCost k/D
  apply (div_lt_div_iff₀ (by linarith : (0:ℝ) < (k:ℝ)+1) hD0).mpr
  dsimp [M] at h1
  nlinarith
