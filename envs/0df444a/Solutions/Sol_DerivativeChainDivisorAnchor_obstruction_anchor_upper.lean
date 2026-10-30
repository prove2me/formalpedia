-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.obstruction_anchor_upper
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:15:49.125833+00:00
-- url     : https://prove2.me/submissions/44f59ae5-63d3-4cf7-9ddd-fad0d2e52c25

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_upper_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadius_drop
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





theorem parameter_upper_identity (k : ℕ) (hk : 3 ≤ k) :
    (orbitCount k : ℝ)*(innerRadius k/(2*(k:ℝ))+(innerRadius k)^2/2)+(k:ℝ) = 3*(k:ℝ)+2 := by
  have hn : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold orbitCount innerRadius
  push_cast
  field_simp
  <;> ring



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor



















theorem solution (k : ℕ) (hk : 3 ≤ k) : obstructionAnchor k < 3*(k:ℝ)+2 := by
  have h := anchor_upper_bound (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le
    (childRadius_bounds k hk).1 (childRadius_bounds k hk).2.le
  have hi : ((orbitCount k-2:ℕ):ℝ)+2 = (orbitCount k:ℝ) := by exact_mod_cast orbit_index k hk
  rw [hi] at h
  have hd := childRadius_drop k hk
  have he := parameter_upper_identity k hk
  change obstructionAnchor k < 3*(k:ℝ)+2
  change rootAnchor (anchorSource (orbitCount k-2) k (innerRadius k))
    (anchorChild (orbitCount k-2) k (childRadius k)) < _
  nlinarith
