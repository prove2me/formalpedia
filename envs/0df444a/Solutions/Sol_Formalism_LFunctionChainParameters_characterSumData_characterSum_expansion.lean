-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.characterSum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:51.182663+00:00
-- url     : https://prove2.me/submissions/4ec8ee0d-9806-4e83-8a29-0147a0f7aecb

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_nsmul
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_vonMangoldt_primePow
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_max_zero_of_gt
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_askD_zero_of_gt
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_local_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_local_split
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_local_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : AskExpansion (H := H) := by
  classical
  intro D hD a t w ha hw N hN
  have step1 : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * (Kc D n g * Fc a t w n g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    simp only [Kc, Fc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun ψ _ => ?_))
    ring
  have step2 : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * (Kc D n g * Fc a t w n g)
      = ∑ n ∈ Icc 1 N, (Λ n : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
          Kc D n g * Fc a t w n g := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i →
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g = 0 := by
    intro p i _ _ hlt
    apply Finset.sum_eq_zero
    intro g hg
    have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
    have hF : Fc a t w (p ^ i) g = 0 := by
      simp only [Fc]
      rw [max_zero_of_gt (m := ((p ^ i : ℕ) : ℝ)) hw hN hg' (by exact_mod_cast hlt), Complex.ofReal_zero]
    rw [hF, mul_zero]
  rw [step1, step2, sum_vonMangoldt_primePow N
    (fun n => ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D n g * Fc a t w n g) hX]
  have hloc : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
      ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
          Kc D (p ^ i) g * Fc a t w (p ^ i) g
        = (((if IsInert D p then 2 * Real.log p * askP D N a t w p else 0)
            + (if p = D.d then Real.log D.d * askD D N a t w else 0) : ℝ) : ℂ) := by
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.1 hp).2
    by_cases hs : p = 2 ∨ p = D.q1
    · rw [local_split D hD N a t w hp' hs]
      have h1 : ¬ IsInert D p := fun h => hs.elim h.2.1 h.2.2.1
      have h2 : p ≠ D.d := fun h => hs.elim (fun h2' => hD.d_ne_two (h.symm.trans h2'))
        (fun hq' => hD.firstPrime_ne_secondPrime (h.symm.trans hq').symm)
      simp [h1, h2]
    · push_neg at hs
      by_cases hdd : p = D.d
      · subst hdd
        rw [local_d D hD N a t w]
        have h1 : ¬ IsInert D D.d := fun h => h.2.2.2.1 rfl
        simp [h1]
      · rw [local_unram D hD N a t w hp' hs.1 hs.2 hdd]
        by_cases hin : IsInert D p
        · simp [hin, hdd]
        · have hphi : InPhi (D.frob p) := by
            by_contra hc
            exact hin ⟨hp', hs.1, hs.2, hdd, hc⟩
          have h0 : askP D N a t w p = 0 := by
            unfold askP
            apply Finset.sum_eq_zero
            intro i hi
            exact absurd (inPhi_nsmul hphi i) (Finset.mem_filter.1 hi).2
          simp [hin, hdd, h0]
  rw [Finset.sum_congr rfl hloc, ← Complex.ofReal_sum]
  unfold ASK
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases hdm : D.d ∈ (range (N + 1)).filter Nat.Prime
    · rw [if_pos hdm]
    · rw [if_neg hdm]
      have hdN : N < D.d := by
        by_contra hc
        apply hdm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hD.d_prime⟩
      rw [askD_zero_of_gt D hD hw hN hdN, mul_zero]
end Formalism.LFunctionChainParameters.characterSumData
