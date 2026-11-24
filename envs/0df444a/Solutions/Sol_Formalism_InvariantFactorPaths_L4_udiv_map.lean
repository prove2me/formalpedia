-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.udiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:43.719245+00:00
-- url     : https://prove2.me/submissions/4bdc9d18-7c7b-4163-9db1-8b269d65d198

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_shift_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_comm_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_step_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_vec
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_cov
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_pow_one
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_pow
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
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section D
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end D
section U
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
private theorem Uop_add_one_apply (c : ℤ) (H : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL (c + 1) Cs a H = Uop p LL c Cs a H + X (Fin.last K, a) * H := by
  rw [Uop_eq, Uop_eq]
  push_cast
  rw [add_smul, one_smul]
  abel
private theorem Uop_pow_succ_apply_eq (c : ℤ) (H : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((Uop p LL c Cs a) ^ (k + 1)) H = ((Uop p LL (c - 1) Cs a) ^ (k + 1)) H +
      ((k + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, a) * ((Uop p LL (c - 1) Cs a) ^ k) H) := by
  have hUV : ∀ Z, Uop p LL c Cs a Z = Uop p LL (c - 1) Cs a Z + X (Fin.last K, a) * Z := by
    intro Z
    have h := Uop_add_one_apply LL Cs a (c - 1) Z
    rwa [sub_add_cancel] at h
  have hsh : ∀ Z, Uop p LL c Cs a (X (Fin.last K, a) * Z) = X (Fin.last K, a) * Uop p LL (c - 1) Cs a Z := by
    intro Z
    have h := Uop_shift LL Cs a (c - 1) 1 _ (DDop_last (p := p) LL Cs a a) Z
    rwa [sub_add_cancel] at h
  induction k with
  | zero => simp [hUV]
  | succ k ih =>
    have e1 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ (k + 1)) H) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1 + 1)) H := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e2 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ k) H) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1)) H := by
      rw [pow_succ' _ k, Module.End.mul_apply]
    rw [pow_succ' (Uop p LL c Cs a) (k + 1), Module.End.mul_apply, ih, map_add, map_smul, hUV, hsh, e1, e2]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_one, map_natCast]
    ring
private theorem Uop_pow_succ_mul_apply (c : ℤ) (x w : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : DDop p LL Cs a x = w) (hw : DDop p LL Cs a w = ((2 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * w))
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((Uop p LL c Cs a) ^ (k + 1)) (x * G) = x * ((Uop p LL c Cs a) ^ (k + 1)) G -
      ((k + 1 : ℕ) : ℚ_[p]) • (w * ((Uop p LL (c - 1) Cs a) ^ k) G) := by
  have h1 : ∀ G, Uop p LL c Cs a (x * G) = x * Uop p LL c Cs a G - w * G := by
    intro G
    rw [Uop_eq, Uop_eq, DDop_mul, hx]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  have hw' : ∀ Y, Uop p LL c Cs a (w * Y) = w * Uop p LL (c - 2) Cs a Y := by
    intro Y
    have h := Uop_shift LL Cs a (c - 2) 2 w hw Y
    rwa [sub_add_cancel] at h
  have hV : ∀ Y, Uop p LL (c - 2) Cs a Y = Uop p LL (c - 1) Cs a Y - X (Fin.last K, a) * Y := by
    intro Y
    have h := Uop_add_one_apply LL Cs a (c - 2) Y
    rw [show c - 2 + 1 = c - 1 by ring] at h
    rw [h]
    abel
  induction k with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_smul]
    exact h1 G
  | succ k ih =>
    have e0 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) (x * G) =
        Uop p LL c Cs a (((Uop p LL c Cs a) ^ (k + 1)) (x * G)) := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e1 : Uop p LL c Cs a (((Uop p LL c Cs a) ^ (k + 1)) G) = ((Uop p LL c Cs a) ^ (k + 1 + 1)) G := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e2 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ k) G) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1)) G := by
      rw [pow_succ' _ k, Module.End.mul_apply]
    rw [e0, ih, map_sub, map_smul, h1, hw', hV, e1, e2, Uop_pow_succ_apply_eq LL Cs a c G k]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_one, map_natCast]
    ring
private theorem inv_factorial_succ_mul_succ_eq (k : ℕ) :
    (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k), one_mul]
end U
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (ha : a ∈ Cs) (P : MvPolynomial (Fin (K + 1) × Fin r) ℤ_[p]) :
    ∀ (c : ℤ) (k : ℕ), ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈
      IntPol p (Fin (K + 1) × Fin r) := by
  have hX : ∀ v, (X v : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun v => FrozenVariableLemmas.intPol_X p v
  have hM : ∀ {F G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]}, F ∈ IntPol p (Fin (K + 1) × Fin r) →
      G ∈ IntPol p (Fin (K + 1) × Fin r) → F * G ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun hF hG => FrozenVariableLemmas.intPol_mul p hF hG
  refine MvPolynomial.induction_on (motive := fun P => ∀ (c : ℤ) (k : ℕ),
    ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈
      IntPol p (Fin (K + 1) × Fin r)) P ?_ ?_ ?_
  · intro z c k
    beta_reduce
    rw [map_C]
    have hC : (C (algebraMap ℤ_[p] ℚ_[p] z) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) =
        (algebraMap ℤ_[p] ℚ_[p] z) • (1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    have hs : ((k.factorial : ℚ_[p]))⁻¹ * ((((k.factorial : ℤ) * Ring.choose c k : ℤ)) : ℚ_[p]) =
        ((Ring.choose c k : ℤ) : ℚ_[p]) := by
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]
    have hT : ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) 1 =
        ((Ring.choose c k : ℤ) : ℚ_[p]) • X (Fin.last K, a) ^ k := by
      rw [Uop_pow_one, smul_smul, hs]
    rw [hC, map_smul, smul_comm, hT, algebraMap_smul, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ z (zsmul_mem (FrozenVariableLemmas.intPol_pow p (hX _) k) _)
  · intro P Q hP hQ c k
    beta_reduce
    rw [map_add, map_add, smul_add]
    exact add_mem (hP c k) (hQ c k)
  · intro P n hP c k
    beta_reduce
    obtain ⟨j, d⟩ := n
    rw [map_mul, map_X, mul_comm]
    have hF0 : map (algebraMap ℤ_[p] ℚ_[p]) P ∈ IntPol p (Fin (K + 1) × Fin r) := by
      simpa using hP c 0
    by_cases hj : j = Fin.last K
    · subst hj
      have key := Uop_shift_pow LL Cs a (c - 1) 1 (X (Fin.last K, d)) (DDop_last LL Cs a d) k
        (map (algebraMap ℤ_[p] ℚ_[p]) P)
      rw [sub_add_cancel] at key
      rw [key, ← mul_smul_comm]
      exact hM (hX _) (hP (c - 1) k)
    · cases hv : LL.vec j with
      | false =>
        by_cases hd : d = a
        · rw [hd]
          have hx : DDop p LL Cs a (X (j, a)) = -(∑ b ∈ Cs, X (Fin.last K, b) * X (j, b)) := by
            rw [DDop_cov LL Cs a j hj hv a, if_pos rfl]
          have hw := DDop_pair (p := p) LL Cs a ha j hj hv
          have hwI : (∑ b ∈ Cs, X (Fin.last K, b) * X (j, b) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈
              IntPol p (Fin (K + 1) × Fin r) :=
            Submodule.sum_mem _ (fun b _ => hM (hX _) (hX _))
          cases k with
          | zero => simpa using hM (hX (j, a)) hF0
          | succ k =>
            rw [Uop_step_pow LL Cs a c _ _ hx hw k, smul_add, smul_smul, inv_factorial_succ_mul_succ_eq]
            simp only [← mul_smul_comm]
            exact add_mem (hM (hX _) (hP c (k + 1))) (hM hwI (hP c k))
        · have hD : DDop p LL Cs a (X (j, d)) = 0 := by
            rw [DDop_cov LL Cs a j hj hv d, if_neg (Ne.symm hd)]
          rw [Uop_comm_pow LL Cs a c _ hD k, ← mul_smul_comm]
          exact hM (hX _) (hP c k)
      | true =>
        by_cases hd : d ∈ Cs
        · have hx : DDop p LL Cs a (X (j, d)) = X (Fin.last K, d) * X (j, a) := by
            rw [DDop_vec LL Cs a j hj hv d, if_pos hd]
          have hw : DDop p LL Cs a (X (Fin.last K, d) * X (j, a)) =
              ((2 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * (X (Fin.last K, d) * X (j, a))) := by
            rw [DDop_mul, DDop_last, DDop_vec LL Cs a j hj hv a, if_pos ha]
            push_cast
            rw [two_smul, one_smul]
            ring
          have hwI : (X (Fin.last K, d) * X (j, a) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈
              IntPol p (Fin (K + 1) × Fin r) := hM (hX _) (hX _)
          cases k with
          | zero => simpa using hM (hX (j, d)) hF0
          | succ k =>
            rw [Uop_pow_succ_mul_apply LL Cs a c _ _ hx hw, smul_sub, smul_smul, inv_factorial_succ_mul_succ_eq]
            simp only [← mul_smul_comm]
            exact sub_mem (hM (hX _) (hP c (k + 1))) (hM hwI (hP (c - 1) k))
        · have hD : DDop p LL Cs a (X (j, d)) = 0 := by
            rw [DDop_vec LL Cs a j hj hv d, if_neg hd]
          rw [Uop_comm_pow LL Cs a c _ hD k, ← mul_smul_comm]
          exact hM (hX _) (hP c k)
end Formalism.InvariantFactorPaths.L4
