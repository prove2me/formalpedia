-- Prove2me | solution 1 for Deduction.ch_balance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:42.436701+00:00
-- url     : https://prove2.me/submissions/2ebcebab-7ea9-4a30-b08f-f59219630f58

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Deduction_CharacterBalance_askExp
import Theorems.Thm_Formalism_D5_Bal_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_partner_inPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_card_notPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_phi_card_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_sum_partner
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_colour_sum
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_inner_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_cut


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
namespace Deduction
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) : (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w := by
  classical
  have hf0 := PB.phi_card_ne_zero (H := H)
  have hfr : ((PhiSet (H := H)).card : ℝ) ≠ 0 := by exact_mod_cast hf0
  rw [CharacterBalance.askExp D hD a t w hw N hN]
  have hin : ∀ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∀ ψ : AddChar (E0 × H) ℂ,
      starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g)))
        + starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' := (Finset.mem_filter.1 hg).2
    have hW := hw _ (partner_inPhi t hg')
    rw [sum_cut D ψ N a _ ha hW (hN _ (partner_inPhi t hg')), inner_eq D ell ψ a _ ha hW]; ring
  rw [Finset.sum_congr rfl (fun g hg => Finset.sum_congr rfl (fun ψ _ => hin g hg ψ))]
  simp only [Finset.sum_add_distrib, mul_add]
  have hDe : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
      ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g)))
      = De D ell a t w := by
    unfold De
    refine congrArg _ (Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun ψ _ => by ring)))
  rw [hDe]
  have hsplit : ∀ g : E0 × H, (∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (if ψ = 0 then
        ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ))
      = ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ) := by
    intro g
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : AddChar (E0 × H) ℂ)), if_pos rfl, AddChar.zero_apply,
      map_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hψ)]
  have hcol : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ))
      = ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * ell chC) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [← Finset.sum_mul, colour_sum ψ, if_neg (Finset.ne_of_mem_erase hψ)])]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.2 ⟨PB.chC_ne_zero (H := H), mem_univ _⟩)]
    ring
  have hreal : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ))
      = ((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, PB.card_notPhi,
      ← Finset.mul_sum, PB.sum_partner t (fun ρ => Real.log (w ρ))]
    simp only [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib, hreal, hcol]
  unfold MAIN
  push_cast
  field_simp
  ring
end Deduction
