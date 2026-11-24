-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gainFactorialInequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:57.68633+00:00
-- url     : https://prove2.me/submissions/732a44fa-dfa7-4511-95b2-a65f71762b6c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_factorialValuationLowerBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_lgN_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_factorial_ge
import Theorems.Thm_Formalism_GrowthSums_oddPowerInvSumIdentity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : StarArith := by
  intro S _ p r0 r1 TT al ls e a i E i0 i2 hp halT he ha hiE hiT hpi htot hi2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨-, hgam⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity (p : ℝ) hp1
  set c : ℝ := 1 / ((p : ℝ) - 1) with hc

  have H1 : ∀ s, (al s : ℝ) * c - (r1 : ℝ) * lgN p (al s) ≤
      ∑ b, (padicValNat p (e s b).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (e s) (al s)
      (fun x _ => by rw [← he s]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x))
    rw [he s, card_univ, Fintype.card_fin] at h
    rw [hc, mul_one_div]
    exact h

  have H3 : ∀ s, ((∑ x, a s x : ℕ) : ℝ) * c - (r0 : ℝ) * r1 * lgN p (ls s) ≤
      ∑ x, (padicValNat p (a s x).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (a s) (ls s)
      (fun x _ => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)) (ha s))
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul] at h
    rw [hc, mul_one_div]
    exact h

  have H2 : ∀ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) * c - ((lgN p (al s) : ℝ)) ^ 2 ≤
      ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) := by
    intro s
    have h1 : ∑ e' ∈ E, ((i s e' : ℝ) / ((p : ℝ) - 1) - lgN p (i s e')) ≤
        ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) :=
      Finset.sum_le_sum (fun e' _ => factorialValuationLowerBound p (i s e') hp)
    have h2 : ((∑ e' ∈ E, lgN p (i s e') : ℕ) : ℝ) ≤ ((lgN p (al s) : ℝ)) ^ 2 := by
      exact_mod_cast sum_lgN_le p hp.one_lt (al s) (i s) E (hpi s)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div] at h1
    rw [Nat.cast_sum] at h2
    rw [hc, mul_one_div, Nat.cast_sum]
    linarith
  have hlg0 : ∀ s, s ∉ TT → ((lgN p (al s) : ℝ)) ^ 2 = 0 := by
    intro s hs
    simp [lgN, halT s hs]
  have hTT_lg : ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2 = ∑ s, ((lgN p (al s) : ℝ)) ^ 2 :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => hlg0 s hs)
  have hTT_al : ∑ s ∈ TT, (al s : ℝ) = ∑ s, (al s : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by rw [halT s hs, Nat.cast_zero])
  have hTT_i : ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by simp [hiT s hs])
  have S1 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H1 s)
  have S2 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H2 s)
  have S3 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H3 s)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at S1 S2 S3
  have htotR : (∑ s, ((∑ x, a s x : ℕ) : ℝ)) + ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) =
      ∑ s, (ls s : ℝ) := by
    exact_mod_cast htot
  have hiR : ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) := by
    push_cast
    rfl
  have hi2R : (p : ℝ) * i2 ≤ ∑ s, (ls s : ℝ) := by exact_mod_cast hi2
  have hL0 : (0 : ℝ) ≤ ∑ s, (ls s : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

  have hgp : 1 / (p : ℝ) ≤ gamP p := by
    unfold gamP rhoP
    have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ hp0 hpp]
    nlinarith
  have hi2g : (i2 : ℝ) ≤ gamP p * ∑ s, (ls s : ℝ) := by
    have h1 : (i2 : ℝ) ≤ 1 / (p : ℝ) * ∑ s, (ls s : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp0]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hgp hL0)
  have hcg : c = gamP p + rhoP p := by rw [hgam]; ring
  unfold deLoss
  rw [hTT_lg, hTT_al, hTT_i, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hcg] at S1 S2 S3
  rw [hiR] at S2 htotR
  set A : ℝ := ∑ s, (al s : ℝ)
  set L : ℝ := ∑ s, (ls s : ℝ)
  set I : ℝ := ∑ s, ∑ e' ∈ E, (i s e' : ℝ)
  set Aa : ℝ := ∑ s, ((∑ x, a s x : ℕ) : ℝ)
  have hAa : Aa = L - I := by linarith
  rw [hAa] at S3
  nlinarith [S1, S2, S3, hi2g]
end Formalism.InvariantFactorPaths.G7
