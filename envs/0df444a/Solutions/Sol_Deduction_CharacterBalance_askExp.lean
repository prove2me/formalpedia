-- Prove2me | solution 1 for Deduction.CharacterBalance.askExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:49.06305+00:00
-- url     : https://prove2.me/submissions/81ef61aa-1b5f-4e83-bced-bb8692b22182

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Deduction_CharacterBalance_ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime
import Theorems.Thm_Deduction_CharacterBalance_lunram
import Theorems.Thm_Deduction_CharacterBalance_lsplit
import Theorems.Thm_Deduction_CharacterBalance_ld
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_nsmul
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_max_zero_of_gt
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_vonMangoldt_primePow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalance
open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalance
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) = (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ) := by
  classical
  set S := univ.filter (fun g : E0 × H => ¬ InPhi g) with hS
  have hA : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) *
        ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 N, (Λ n : ℂ) * ∑ g ∈ S, Kc D n g * Fc a t w n g := by
    calc _ = ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ∑ n ∈ Icc 1 N, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) := by
          simp only [Finset.mul_sum]
      _ = ∑ g ∈ S, ∑ n ∈ Icc 1 N, ∑ ψ : AddChar (E0 × H) ℂ, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) :=
          Finset.sum_congr rfl (fun g _ => Finset.sum_comm)
      _ = ∑ n ∈ Icc 1 N, ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) :=
          Finset.sum_comm
      _ = _ := by
          simp only [Kc, Fc, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun g _ =>
            Finset.sum_congr rfl (fun ψ _ => by ring)))
  rw [hA]
  rw [sum_vonMangoldt_primePow N (fun n => ∑ g ∈ S, Kc D n g * Fc a t w n g) (by
    intro p i hp hi hgt
    refine Finset.sum_eq_zero (fun g hg => ?_)
    have hg' := (Finset.mem_filter.1 hg).2
    unfold Fc
    rw [max_zero_of_gt hw hN hg' (m := ((p ^ i : ℕ) : ℝ)) (by exact_mod_cast hgt)]
    simp)]
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hC : ∀ p ∈ P, (∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ S, Kc D (p ^ i) g * Fc a t w (p ^ i) g)
      = (if IsInert D p then ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) else 0)
        + (if p = D.d then ((Real.log D.d * askD D N a t w : ℝ) : ℂ) else 0) := by
    intro p hpP
    have hp : p.Prime := (Finset.mem_filter.1 hpP).2
    by_cases hd : p = D.d
    · subst hd
      rw [hS, ld D hD N a t w, if_neg (fun h => h.2.2.2.1 rfl), if_pos rfl, zero_add]
    · rw [if_neg hd, add_zero]
      by_cases h2 : p ∈ S0
      · rw [hS, lsplit D hD N a t w hp h2]
        rw [if_neg]
        rintro ⟨_, _, _, _, hc⟩
        exact hc (hD.split_frob p h2)
      · have h21 : p ≠ 2 := fun e => h2 (e ▸ hD.two_mem)
        have h22 : p ≠ D.q1 := fun e => h2 (e ▸ hD.q1_mem)
        rw [hS, lunram D hD N a t w hp h2 hd]
        by_cases hin : IsInert D p
        · rw [if_pos hin]
        · rw [if_neg hin]
          have hφ : InPhi (D.frob p) := by
            by_contra hc; exact hin ⟨hp, h21, h22, hd, hc⟩
          have : askP D N a t w p = 0 := by
            unfold askP
            rw [Finset.sum_eq_zero]
            intro i hi
            exact absurd (inPhi_nsmul hφ i) (Finset.mem_filter.1 hi).2
          rw [this]; simp
  rw [Finset.sum_congr rfl hC, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq']
  have hfilt : (range (N + 1)).filter (IsInert D) = P.filter (IsInert D) := by
    rw [hP, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩)
  unfold ASK
  rw [hfilt]
  push_cast
  congr 1
  by_cases hdP : D.d ∈ P
  · rw [if_pos hdP]
  · rw [if_neg hdP]
    have hdN : N < D.d := by
      by_contra hc
      exact hdP (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hD.d_prime⟩)
    rw [ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime D hD hw hN hdN]; simp
end Deduction.CharacterBalance
