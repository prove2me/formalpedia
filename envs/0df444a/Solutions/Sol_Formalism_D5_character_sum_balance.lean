-- Prove2me | solution 1 for Formalism.D5.character_sum_balance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:49.692397+00:00
-- url     : https://prove2.me/submissions/491c0c2a-8177-4597-ace5-30d891408201

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_sum_S_rho
import Theorems.Thm_Formalism_D5_Bal_card_S
import Theorems.Thm_Formalism_D5_Bal_card_G_eq
import Theorems.Thm_Formalism_D5_Bal_phiSet_card_ne_zero
import Theorems.Thm_Formalism_D5_Bal_chC_ne_zero
import Theorems.Thm_Formalism_D5_Bal_sum_S_char
import Theorems.Thm_Formalism_D5_Bal_askC_eq

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
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Bal
namespace Formalism.D5
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : Balance (H := H) := by
  intro Hs a t w ha hw
  have hf0 := phiSet_card_ne_zero (H := H)
  have hfr : ((PhiSet (H := H)).card : ℝ) ≠ 0 := by exact_mod_cast hf0
  have hG := card_G_eq (H := H)

  have hask : askTop Hs a t w = ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
          + ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ))).re := by
    unfold askTop vonMangoldtClassSum
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have e1 : (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ∑ n ∈ Icc 1 ⌊a / w (cconj + g + topPl t)⌋₊,
          (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w (cconj + g + topPl t) : ℝ) : ℂ))
        = ∑ ψ : AddChar (E0 × H) ℂ,
        (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
          + ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)) :=
      Finset.sum_congr rfl (fun ψ _ => by rw [askC_eq Hs ψ a _ ha (hw _)]; ring)
    rw [e1, hG]
    rw [show (1 / ((PhiSet (H := H)).card : ℂ)) = ((2 : ℝ) : ℂ) * (1 / (2 * ((PhiSet (H := H)).card : ℂ))) by
      push_cast; field_simp, mul_assoc, Complex.re_ofReal_mul]

  have hsplit : ∀ g : E0 × H, (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * (if ψ = 0 then
        ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ))
      = ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), ψ (-g) * (-(a : ℂ) * Hs.ell ψ) := by
    intro g
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : AddChar (E0 × H) ℂ)), if_pos rfl, AddChar.zero_apply, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hψ)]
  have hcol : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
        ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), ψ (-g) * (-(a : ℂ) * Hs.ell ψ))
      = ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [← Finset.sum_mul, sum_S_char Hs t ψ (Finset.ne_of_mem_erase hψ)])]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.2 ⟨chC_ne_zero Hs, mem_univ _⟩)]
    ring
  have hreal : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
        ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ))
      = ((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, card_S,
      ← Finset.mul_sum, sum_S_rho t (fun ρ => Real.log (w ρ))]
    simp only [nsmul_eq_mul]
    ring
  have hY : ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)).re
      = ledTop Hs a w := by
    rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib, hreal, hcol]
    have e2 : (1 / ((PhiSet (H := H)).card : ℂ)) *
        (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ)
          + ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC))
        = (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ)) / ((PhiSet (H := H)).card : ℝ) : ℝ) : ℂ)
          + (a : ℂ) * Hs.ell Hs.chC := by
      rw [Complex.ofReal_div, Complex.ofReal_natCast]
      field_simp
    rw [e2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    unfold ledTop
    field_simp
    ring
  rw [hask, Finset.sum_congr rfl (fun g _ => Finset.sum_add_distrib), Finset.sum_add_distrib, mul_add,
    Complex.add_re, hY]
  unfold balTop
  ring
end Formalism.D5
