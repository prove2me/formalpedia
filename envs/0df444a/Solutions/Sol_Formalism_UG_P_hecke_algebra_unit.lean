-- Prove2me | solution 1 for Formalism.UG.P.hecke_algebra_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:38.234845+00:00
-- url     : https://prove2.me/submissions/9dffe005-f82c-4b46-965d-87e7f141daac

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Theorems.Thm_Formalism_UG_P_mem_dc_one
import Theorems.Thm_Formalism_UG_P_mem_hecke_iff
import Theorems.Thm_Formalism_UG_P_dosetInd_of_mem
import Theorems.Thm_Formalism_UG_P_dosetInd_of_not_mem
import Theorems.Thm_Formalism_UG_P_out_mem_of_eq_one
import Theorems.Thm_Formalism_UG_P_out_not_mem_of_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeUnit := by
  unfold Formalism.UG.HeckeUnit
  intro G _ K k _ f hf
  unfold conv
  have hb := ((mem_hecke_iff k K f).1 hf).1
  have h1 : ∀ y : G, dosetInd k K 1 y = if y ∈ K then 1 else 0 := by
    intro y
    by_cases hy : y ∈ K
    · rw [if_pos hy, dosetInd_of_mem]
      exact (mem_dc_one K y).2 hy
    · rw [if_neg hy, dosetInd_of_not_mem]
      exact fun h => hy ((mem_dc_one K y).1 h)
  refine ⟨funext fun g => ?_, funext fun g => ?_⟩
  · show ∑ᶠ x : G ⧸ K, dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g) = f g
    have e := finsum_eq_single
      (fun x : G ⧸ K => dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g))
      ((1 : G) : G ⧸ K) (fun x hx => by
        show dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g) = 0
        rw [h1, if_neg (out_not_mem_of_ne_one K x hx), zero_mul])
    rw [e]
    have hm := out_mem_of_eq_one K ((1 : G) : G ⧸ K) rfl
    rw [h1, if_pos hm, one_mul]
    have := hb ⟨(Quotient.out ((1 : G) : G ⧸ K))⁻¹, K.inv_mem hm⟩ 1 g
    simpa using this
  · show ∑ᶠ x : G ⧸ K, f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g) = f g
    have e := finsum_eq_single
      (fun x : G ⧸ K => f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g))
      ((g : G) : G ⧸ K) (fun x hx => by
        show f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g) = 0
        have hm : (Quotient.out x)⁻¹ * g ∉ K := by
          intro h
          apply hx
          rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
          exact h
        rw [h1, if_neg hm, mul_zero])
    rw [e]
    have hm : (Quotient.out ((g : G) : G ⧸ K))⁻¹ * g ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [h1, if_pos hm, mul_one]
    have := (hb 1 ⟨(Quotient.out ((g : G) : G ⧸ K))⁻¹ * g, hm⟩ (Quotient.out ((g : G) : G ⧸ K))).symm
    simpa using this
end Formalism.UG.P
