-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.childRadius_drop
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:13:46.292959+00:00
-- url     : https://prove2.me/submissions/65edf7d9-5b35-49e2-9a28-6ff4ea86f8a7

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
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







theorem childRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < childRadius k ∧ childRadius k < 1 := by
  have hp := childRadiusPower_bounds k hk
  unfold childRadius
  exact ⟨Real.rpow_pos_of_pos hp.1 _, Real.rpow_lt_one hp.1.le hp.2.1
    (inv_pos.mpr (by exact_mod_cast orbitCount_pos k hk))⟩

theorem childRadius_pow (k : ℕ) (hk : 3 ≤ k) :
    childRadius k ^ orbitCount k = (1+((k:ℝ)-1)*innerRadius k ^ orbitCount k)/(k:ℝ) := by
  unfold childRadius
  exact Real.rpow_inv_natCast_pow (childRadiusPower_bounds k hk).1.le (orbitCount_pos k hk).ne'







end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainDivisorAnchor



















theorem solution (k : ℕ) (hk : 3 ≤ k) :
    (orbitCount k : ℝ)*(1-childRadius k) ≤ (k:ℝ)-1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb := childRadius_bounds k hk
  have hp : 1/(k:ℝ) ≤ childRadius k ^ orbitCount k := by
    rw [childRadius_pow k hk]
    exact (childRadiusPower_bounds k hk).2.2
  have hsum : (orbitCount k : ℝ)*childRadius k ^ orbitCount k ≤
      ∑ j ∈ Finset.range (orbitCount k), childRadius k ^ j := by
    calc
      _ = ∑ _j ∈ Finset.range (orbitCount k), childRadius k ^ orbitCount k := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        pow_le_pow_of_le_one hb.1.le hb.2.le (Finset.mem_range.mp hj).le
  have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hb.2.le)
  rw [geom_sum_mul_neg] at hmul
  have hdiv : (orbitCount k : ℝ)*(1-childRadius k)/(k:ℝ) ≤ 1-1/(k:ℝ) := by
    calc
      _ = (orbitCount k : ℝ)*(1-childRadius k)*(1/(k:ℝ)) := by ring
      _ ≤ (orbitCount k : ℝ)*(1-childRadius k)*(childRadius k ^ orbitCount k) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hb.2.le))
      _ ≤ 1-childRadius k ^ orbitCount k := by nlinarith
      _ ≤ _ := by linarith
  have h := (div_le_iff₀ hk0).mp hdiv
  have he : (1-1/(k:ℝ))*(k:ℝ) = (k:ℝ)-1 := by field_simp
  simpa only [he] using h
