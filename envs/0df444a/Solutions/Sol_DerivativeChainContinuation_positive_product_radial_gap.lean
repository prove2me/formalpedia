-- Prove2me | solution 1 for DerivativeChainContinuation.positive_product_radial_gap
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:36:55.869977+00:00
-- url     : https://prove2.me/submissions/df2ee02d-4f70-438e-855d-12057252d96e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_power_midpoint_strict
import Theorems.Thm_DerivativeChainContinuation_positive_weighted_outer_midpoint
import Theorems.Thm_DerivativeChainContinuation_positive_weighted_single_radius
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n s k : ℕ) (a : Fin (n+1) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 2 ≤ k)
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ v : ℝ,0<v → (positiveWeighted s k (realRootProduct a)).eval v=0 → v ≤ t)
    (R x y : ℝ) (hR : 0 ≤ R) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hRpow : R^k=a (Fin.last n)) (hxpow : x^k=t)
    (hparent : y=0 ∨ ∃ i : Fin (n+1),y^k=a i) (hyR : y<R) : R+y<2*x := by
  cases n with
  | zero =>
    have hQ : realRootProduct a=X-C (a 0) := by simp [realRootProduct]
    have hb : a 0<(2 : ℝ)^k*t := positive_weighted_single_radius s k hk (a 0) t
      ht (by rwa [←hQ])
    rcases hparent with rfl | ⟨i,hi⟩
    · have hpow : R^k<(2*x)^k := by rw [mul_pow,hxpow,hRpow]; simpa using hb
      have hRx : R<2*x := by
        by_contra hn
        have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*x) (le_of_not_gt hn) k
        exact (not_lt_of_ge hh) hpow
      linarith
    · have he : y=R := (pow_left_inj₀ hy hR (show k≠0 by omega)).mp (by
        rw [hi,hRpow,Fin.eq_zero i,Fin.last_zero])
      linarith
  | succ d =>
    have hmid := positive_weighted_outer_midpoint d s k a ha hpositive (by omega) t ht hroot hmax
    rcases hparent with rfl | ⟨i,hi⟩
    · have hRpos : 0<R := by
        by_contra hn
        have he : R=0 := le_antisymm (le_of_not_gt hn) hR
        rw [he,zero_pow (show k≠0 by omega)] at hRpow
        have hp := hpositive (Fin.last (d+1))
        linarith
      have hm : ((0 : ℝ)^k+R^k)/2 ≤ x^k := by
        rw [zero_pow (show k≠0 by omega),hRpow,hxpow]
        have hp := hpositive (Fin.last d).castSucc
        linarith
      have hh := positive_power_midpoint_strict k hk 0 R x le_rfl hRpos hx hm
      linarith
    · have hi' : i≠Fin.last (d+1) := by
        intro he
        have hey : y=R := (pow_left_inj₀ hy hR (show k≠0 by omega)).mp (by rw [hi,he,hRpow])
        linarith
      have hiA : a i ≤ a (Fin.last d).castSucc := ha (by
        have hlt : i<Fin.last (d+1) := lt_of_le_of_ne (Fin.le_last _) hi'
        change i.val ≤ d
        have hh : i.val<d+1 := hlt
        omega)
      have hm : (y^k+R^k)/2 ≤ x^k := by rw [hi,hRpow,hxpow]; linarith
      have hh := positive_power_midpoint_strict k hk y R x hy hyR hx hm
      linarith
