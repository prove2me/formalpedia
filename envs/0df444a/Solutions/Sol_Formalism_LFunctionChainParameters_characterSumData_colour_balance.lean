-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.colour_balance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:49.432804+00:00
-- url     : https://prove2.me/submissions/aa0a5848-dd91-4c80-ae73-1f6c8a0c05a0

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_sum_partner
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_card_notPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_phi_card_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_colour_sum
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_characterSum_expansion
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_cut
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_inner_eq
import Theorems.Thm_Formalism_D5_Bal_chC_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
namespace PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem zero_apply_lemma (g : E0 × H) : (0 : AddChar (E0 × H) ℂ) g = 1 := by
  first
  | exact AddChar.zero_apply g
  | rfl
  | simp
end
end PB
open PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end Formalism.LFunctionChainParameters.characterSumData
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : AskMainBalance (H := H) := by
  classical
  intro D hD ell a t w ha hw N hN
  rw [characterSum_expansion D hD a t w ha hw N hN]
  have hinner : ∀ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∀ ψ : AddChar (E0 × H) ℂ,
      ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
        = ((w (partner t g) : ℝ) : ℂ) * GPsi D ell ψ (a / w (partner t g))
          + (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
    have hρ := partner_inPhi t hg'
    rw [sum_cut D ψ N a (w (partner t g)) ha (hw _ hρ) (hN _ hρ),
      inner_eq D ell ψ a (w (partner t g)) ha (hw _ hρ)]
  have hsum : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * ((w (partner t g) : ℝ) : ℂ) * GPsi D ell ψ (a / w (partner t g))
        + ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [hinner g hg ψ]
    ring
  have hcorr : ∀ ψ : AddChar (E0 × H) ℂ, ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ)
      = (if ψ = 0 then ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
            ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else 0)
        + (if ψ = chC then (a : ℂ) * ell chC * ((PhiSet (H := H)).card : ℂ) else 0) := by
    intro ψ
    by_cases h0 : ψ = 0
    · have h1 : ¬ ψ = chC := fun h => chC_ne_zero (h ▸ h0)
      rw [if_pos h0, if_neg h1, add_zero]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [if_pos h0, h0, zero_apply_lemma, map_one, one_mul]
    · rw [if_neg h0, zero_add]
      simp only [if_neg h0]
      rw [← Finset.sum_mul, colour_sum ψ, if_neg h0]
      by_cases h1 : ψ = chC
      · rw [if_pos h1, if_pos h1, h1]
        ring
      · rw [if_neg h1, if_neg h1, zero_mul]
  have hB : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
            ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + (a : ℂ) * ell chC * ((PhiSet (H := H)).card : ℂ) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun ψ _ => hcorr ψ), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hC : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        (a * Real.log a - a * Real.log (w (partner t g)) - (1 + Real.eulerMascheroniConstant) * a)
      = ((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
        - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum, sum_partner t (fun ρ => Real.log (w ρ)), card_notPhi]
    simp only [nsmul_eq_mul]
    ring
  rw [hsum, hB, ← Complex.ofReal_sum, hC]
  have hΦ := phi_card_ne_zero (H := H)
  unfold De MAIN
  push_cast
  field_simp
  ring
end Formalism.LFunctionChainParameters.characterSumData
