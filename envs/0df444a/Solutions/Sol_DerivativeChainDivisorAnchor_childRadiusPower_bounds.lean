-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.childRadiusPower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:04:31.696082+00:00
-- url     : https://prove2.me/submissions/c4db0f99-5b00-4503-ad10-edc466e7733a

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorParameters
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



theorem innerRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < innerRadius k ∧ innerRadius k < 1 := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hs : (0:ℝ) < (k:ℝ)^2 := by positivity
  unfold innerRadius
  constructor
  · positivity
  · apply (div_lt_one hs).mpr
    nlinarith













end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainDivisorAnchor













theorem solution (k : ℕ) (hk : 3 ≤ k) :
    0 < childRadiusPower k ∧ childRadiusPower k < 1 ∧ 1/(k:ℝ) ≤ childRadiusPower k := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have ha := innerRadius_bounds k hk
  have hp0 : 0 < innerRadius k ^ orbitCount k := pow_pos ha.1 _
  have hp1 : innerRadius k ^ orbitCount k < 1 := pow_lt_one₀ ha.1.le ha.2 (orbitCount_pos k hk).ne'
  have hkm : (0:ℝ) < (k:ℝ)-1 := by linarith
  unfold childRadiusPower
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_lt_one hk0).mpr
    nlinarith [mul_pos (by linarith : (0:ℝ) < (k:ℝ)-1) (sub_pos.mpr hp1)]
  · apply (div_le_div_iff_of_pos_right hk0).mpr
    nlinarith
