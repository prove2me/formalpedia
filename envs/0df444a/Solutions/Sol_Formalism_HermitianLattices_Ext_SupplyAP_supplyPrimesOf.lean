-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:57.743491+00:00
-- url     : https://prove2.me/submissions/df425d01-e035-4b90-97f7-c607a43af4d7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_progSupplyOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (A : ℕ) (hA : ExcBoundAt A) : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.card = n ∧
    ∀ q ∈ S, q.Prime ∧ q ≡ 1 [MOD m] ∧ (q : ℝ) ≤ Real.exp (C * Real.log (2 * m * (n + 2)) ^ 2) := by
  obtain ⟨K, hK, hP⟩ := progSupplyOf A hA
  refine ⟨K, by linarith, fun m n hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set ℓ := Real.log (2 * (m : ℝ) * ((n : ℝ) + 2)) with hℓdef
  set x := Real.exp (K * ℓ ^ 2) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have h30 : 0 ≤ Real.log (3 * (m : ℝ)) := Real.log_nonneg (by linarith)
  have h3 : Real.log (3 * (m : ℝ)) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hcond : K * Real.log (3 * (m : ℝ)) ^ 2 ≤ Real.log x := by
    rw [hxdef, Real.log_exp]
    have := pow_le_pow_left₀ h30 h3 2
    nlinarith
  have hcard := hP m 1 x hm (Nat.coprime_one_left m) hcond
  have hℓ1 : Real.log ((n : ℝ) + 2) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hℓ4 : Real.log 4 ≤ ℓ := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) h2
  have hsq : Real.sqrt x = Real.exp (K * ℓ ^ 2 / 2) := by
    have he : Real.exp (K * ℓ ^ 2) = Real.exp (K * ℓ ^ 2 / 2) * Real.exp (K * ℓ ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hxdef, he, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hnx : (n : ℝ) ≤ Real.sqrt x := by
    rw [hsq]
    calc (n : ℝ) ≤ (n : ℝ) + 2 := by linarith
      _ = Real.exp (Real.log ((n : ℝ) + 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (K * ℓ ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hn : n ≤ (primesAP m 1 x).card := by exact_mod_cast hnx.trans hcard
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨S, hScard, fun q hq => ?_⟩
  have hmem := hSsub hq
  simp only [primesAP, Finset.mem_filter, Finset.mem_Icc] at hmem
  obtain ⟨⟨_, hqx⟩, hqp, hqm⟩ := hmem
  refine ⟨hqp, hqm, ?_⟩
  exact (Nat.cast_le.mpr hqx).trans (Nat.floor_le hx0.le)
end Formalism.HermitianLattices.Ext.SupplyAP
