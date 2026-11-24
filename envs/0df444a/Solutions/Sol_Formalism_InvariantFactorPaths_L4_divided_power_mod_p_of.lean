-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.divided_power_mod_p_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:39.781698+00:00
-- url     : https://prove2.me/submissions/05e02c9f-1fc8-45a0-95fe-cfa1b32f7b99

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_p_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mod_p_of_conditions
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_early_letters_mod_p
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_last_letter_mod_p
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compP_mem_intPol
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_int_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_multiDeg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pol_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : DivModPOf := by
  classical
  intro p _ K r _ LL q J M ρ hv hlift h hY hint a ha b hb heq
  set a' := compP (fun m' => MultiDeg LL (Finsupp.single (Fin.last K, ρ) 1 + m')) a with ha'
  set b' := compP (fun m => MultiDeg LL m) b with hb'
  have ha'int : a' ∈ IntPol p (Fin (K + 1) × Fin r) := compP_mem_intPol _ a ha
  have hb'int : b' ∈ IntPol p (Fin (K + 1) × Fin r) := compP_mem_intPol _ b hb
  have hpol : h ∈ Pol p r LL := hY.1
  unfold Pol at hpol
  rw [mem_restrictSupport_iff] at hpol
  have heq' : h = X (Fin.last K, ρ) * a' + (p : ℚ_[p]) • b' := by
    ext m
    have h0 := congrArg (coeff m) heq
    rw [coeff_add, coeff_smul, coeff_X_mul'] at h0
    rw [coeff_add, coeff_smul, coeff_X_mul', coeff_compP, coeff_compP]
    by_cases hm : MultiDeg LL m
    · rw [h0, if_pos hm]
      congr 1
      split_ifs with hs h1
      · rfl
      · exfalso
        apply h1
        rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
          (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))]
        exact hm
      · rfl
    · have hz : coeff m h = 0 := by
        by_contra hne
        exact hm (hpol (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))
      rw [hz, if_neg hm, smul_zero, add_zero]
      split_ifs with hs h1
      · exfalso
        rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
          (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))] at h1
        exact hm h1
      · rfl
      · rfl
  by_cases ho : LL.deg (Fin.last K) = 0
  · have hz : a' = 0 := by
      ext m
      rw [coeff_compP, if_neg, coeff_zero]
      intro hm
      have h1 := hm (Fin.last K)
      rw [ho] at h1
      have h2 := (Finset.sum_eq_zero_iff.mp h1) ρ (Finset.mem_univ _)
      simp at h2
    refine ⟨0, Submodule.zero_mem _, b', hb'int, by rw [mul_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [heq', hz]
  · have he : 1 ≤ LL.deg (Fin.last K) := Nat.one_le_iff_ne_zero.mpr ho
    have ha'pol : a' ∈ Pol p r (setLast LL (LL.deg (Fin.last K) - 1)) := by
      unfold Pol
      rw [mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe, mem_support_iff, coeff_compP] at hm
      split_ifs at hm with h1
      · exact (multiDeg_pow LL ρ 1 he m).1 h1
      · exact absurd rfl hm
    have hXa : ∀ k, ModCond p LL (J k) (M k) (X (Fin.last K, ρ) * a') := by
      intro k
      have e : X (Fin.last K, ρ) * a' = h - (p : ℚ_[p]) • b' := by rw [heq']; abel
      rw [e]
      exact modCond_sub p LL _ _ _ _ (mod_p_of_conditions p (K + 1) r LL _ _ h ((Submodule.mem_iInf _).1 hY.2 k))
        (modCond_p_smul p LL _ _ b' hb'int)
    have hak : ∀ k, ModCond p (setLast LL (LL.deg (Fin.last K) - 1)) (J k) (shiftLastLetterThresholds K J M 1 k) a' := by
      intro k
      show ModCond p LL (J k) (shiftLastLetterThresholds K J M 1 k) a'
      unfold shiftLastLetterThresholds
      split_ifs with hk
      · rw [Nat.cast_one]
        exact mul_last_letter_mod_p p K r LL (J k) (M k) ρ a' hk hv (hXa k)
      · exact mul_early_letters_mod_p p K r LL (J k) (M k) ρ a' (by omega) (hXa k)
    obtain ⟨h1, hh1Y, hh1int, b1, hb1, e1⟩ := hlift a' ⟨ha'pol, ha'int⟩ hak
    refine ⟨h1, hh1int, X (Fin.last K, ρ) * b1 + b',
      Submodule.add_mem _ ((X_mul_int_iff _ _).2 hb1) hb'int, ⟨?_, ?_⟩, ?_⟩
    · have := (pol_pow (p := p) LL ρ 1 he h1).2 hh1Y.1
      rwa [pow_one] at this
    · rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro k
      have := (yCond_pow (p := p) LL hv ρ 1 (J k) (M k) h1).2 ((Submodule.mem_iInf _).1 hh1Y.2 k)
      rwa [pow_one] at this
    · rw [heq', e1, mul_add, mul_smul_comm, smul_add, add_assoc]
end Formalism.InvariantFactorPaths.L4
