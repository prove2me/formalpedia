-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.divPow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:00.951444+00:00
-- url     : https://prove2.me/submissions/5722f417-d9c0-41b5-8851-5c490ce3fdb9

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (D : A →ₗ[K] A) (hD : ∀ a b, D (a * b) = a * D b + b * D a) (k : ℕ) (f g : A) :
    ((k.factorial : K))⁻¹ • (D ^ k) (f * g) =
      ∑ ij ∈ antidiagonal k, (((ij.1.factorial : K))⁻¹ • (D ^ ij.1) f) * (((ij.2.factorial : K))⁻¹ • (D ^ ij.2) g) := by
  let dd : ℕ → A → A := fun k f => ((k.factorial : K))⁻¹ • (D ^ k) f
  have hdd : ∀ k f, dd k f = ((k.factorial : K))⁻¹ • (D ^ k) f := fun _ _ => rfl
  have hD1 : ∀ k f, D (dd k f) = ((k + 1 : ℕ) : K) • dd (k + 1) f := by
    intro k f
    rw [hdd, hdd, map_smul, pow_succ', Module.End.mul_apply, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h1 : ((k.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2 : ((k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  show dd k (f * g) = ∑ ij ∈ antidiagonal k, dd ij.1 f * dd ij.2 g
  induction k with
  | zero => simp [hdd]
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hL : dd (k + 1) (f * g) = ((k + 1 : ℕ) : K)⁻¹ • D (dd k (f * g)) := by
      rw [hD1, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [hL, ih, map_sum]
    simp only [hD, hD1, mul_smul_comm, Finset.sum_add_distrib]
    rw [inv_smul_eq_iff₀ hk]
    have hsplit : ((k + 1 : ℕ) : K) • ∑ ij ∈ antidiagonal (k + 1), dd ij.1 f * dd ij.2 g
        = ∑ ij ∈ antidiagonal (k + 1), ((ij.2 : ℕ) : K) • (dd ij.1 f * dd ij.2 g)
          + ∑ ij ∈ antidiagonal (k + 1), ((ij.1 : ℕ) : K) • (dd ij.1 f * dd ij.2 g) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have hij' : ij.1 + ij.2 = k + 1 := by simpa using hij
      rw [← add_smul, ← Nat.cast_add, add_comm ij.2, hij']
    rw [hsplit, Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [mul_comm]
end Formalism.InvariantFactorPaths.PW
