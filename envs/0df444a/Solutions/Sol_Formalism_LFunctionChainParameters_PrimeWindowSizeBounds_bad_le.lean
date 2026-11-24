-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.bad_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:35.520779+00:00
-- url     : https://prove2.me/submissions/736c760b-3e3a-4b54-8f0c-04196f66bd5a

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_prime_log_sum_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution {τ : Type} (P : Par) (Ps sB : Finset ℕ) (cl : ℕ → PClass) (TT : Finset τ)
    (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop) (m : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ P.a) (hβ : 0 ≤ P.β)
    (hX : 1 ≤ P.Xp) (hsB : ∀ p ∈ sB, p.Prime ∧ (p : ℝ) ≤ P.Xp)
    (hTops : ∑ p ∈ sB, 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) ≤
      32 * P.β * m * P.a * TT.card * ∑ p ∈ sB, Real.log p / p)
    (hBad : ∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ sB ∧ BAD p t) :
    ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * P.a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤ tBad P m TT.card := by
  have hco : ∀ p : ℕ, 0 ≤ 4 * m * P.a * (Real.log p / p) := fun p => by
    have : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    positivity
  have h1 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * P.a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ sB then 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hb := hBad p hp.1 hp.2
    by_cases hps : p ∈ sB
    · rw [if_pos hps]
      refine mul_le_mul_of_nonneg_left ?_ (hco p)
      have hsub : TT \ TTp p ⊆ TT.filter fun t => BAD p t := by
        intro t ht
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.1 ht).1, (hb t ht).2⟩
      exact_mod_cast Finset.card_le_card hsub
    · rw [if_neg hps]
      have hemp : TT \ TTp p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        exact hps (hb t ht).1
      rw [hemp]; simp
  have h2 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ sB then 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) ≤
      ∑ p ∈ sB, 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hco p) (Nat.cast_nonneg _))
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have h3 := prime_log_sum_bound P.Xp sB hX hsB
  have h4 : 32 * P.β * m * P.a * TT.card * ∑ p ∈ sB, Real.log p / p ≤
      32 * P.β * m * P.a * TT.card * (Real.log P.Xp + Real.log 4) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  unfold tBad
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
