-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.lower_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:17.887778+00:00
-- url     : https://prove2.me/submissions/99ecee04-c764-482b-8a2c-0e98bc0d2f47

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution [CharZero K] (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {z i : ι} (hiz : i ≠ z) {y : W} (hy : y ∈ NN) (he : E i z y = 0) (hii : E i i y = 0) (hzz : E z z y = 0) :
    E z i y = 0 := by
  have hpow : ∀ k, (E z i ^ (k + 1)) y = E z i ((E z i ^ k) y) := by
    intro k; rw [pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, (E z i ^ k) y ∈ NN := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih => rw [hpow]; exact hN _ _ _ ih
  have sZ : E z z * E z i = E z i * E z z + E z i := by
    rw [h.sw z z z i, if_pos (rfl : z = z), if_neg hiz, sub_zero]
  have sI : E i i * E z i = E z i * E i i - E z i := by
    rw [h.sw i i z i, if_neg hiz, if_pos (rfl : i = i), zero_sub, ← sub_eq_add_neg]
  have sE : E i z * E z i = E z i * E i z + (E i i - E z z) := by
    rw [h.sw i z z i, if_pos (rfl : z = z), if_pos (rfl : i = i)]
  have wZ : ∀ k : ℕ, E z z ((E z i ^ k) y) = (k : K) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero => simp [hzz]
    | succ k ih =>
      rw [hpow, ← Module.End.mul_apply (E z z), sZ, LinearMap.add_apply, Module.End.mul_apply, ih, map_smul]
      push_cast
      module
  have wI : ∀ k : ℕ, E i i ((E z i ^ k) y) = -(k : K) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero => simp [hii]
    | succ k ih =>
      rw [hpow, ← Module.End.mul_apply (E i i), sI, LinearMap.sub_apply, Module.End.mul_apply, ih, map_smul]
      push_cast
      module
  have wE : ∀ k : ℕ, E i z ((E z i ^ (k + 1)) y) = -(((k : K) + 1) * (k : K)) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero =>
      rw [hpow, ← Module.End.mul_apply (E i z), sE]
      simp [he, hii, hzz]
    | succ k ih =>
      rw [hpow (k + 1), ← Module.End.mul_apply (E i z), sE, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.mul_apply, ih, map_smul, wI, wZ, ← hpow]
      push_cast
      module
  have top : ∀ k : ℕ, l < k → (E z i ^ k) y = 0 := by
    intro k hk
    exact hev z (k : ℤ) _ (hmem k) (by rw [wZ k, Int.cast_natCast])
      (by rw [Nat.abs_cast]; exact_mod_cast hk)
  have down : ∀ n : ℕ, ∀ k : ℕ, k + n = l + 1 → 1 ≤ k → (E z i ^ k) y = 0 := by
    intro n
    induction n with
    | zero => intro k hk _; exact top k (by omega)
    | succ n ih =>
      intro k hk hk1
      have h1 : (E z i ^ (k + 1)) y = 0 := ih (k + 1) (by omega) (by omega)
      have h2 := wE k
      rw [h1, map_zero] at h2
      have hk0 : (k : K) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have hk2 : (k : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      exact (smul_eq_zero.mp h2.symm).resolve_left (neg_ne_zero.mpr (mul_ne_zero hk2 hk0))
  have := down l 1 (by omega) le_rfl
  simpa using this
end Formalism.InvariantFactorPaths.PW
