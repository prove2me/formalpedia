-- Prove2me | solution 1 for Formalism.UG.P.hecke_action_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:26.909586+00:00
-- url     : https://prove2.me/submissions/3dd52732-4147-4162-8a9c-e95a7f1bba43

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Theorems.Thm_Formalism_UG_P_mem_dc_one
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
theorem _root_.solution : Formalism.UG.HeckeActOne := by
  unfold Formalism.UG.HeckeActOne
  intro G _ Γ K k _ W _ _ ρ φ hφ
  unfold hAct
  have h1 : ∀ y : G, dosetInd k K 1 y = if y ∈ K then 1 else 0 := by
    intro y
    by_cases hy : y ∈ K
    · rw [if_pos hy, dosetInd_of_mem]
      exact (mem_dc_one K y).2 hy
    · rw [if_neg hy, dosetInd_of_not_mem]
      exact fun h => hy ((mem_dc_one K y).1 h)
  refine funext fun g => ?_
  show ∑ᶠ x : G ⧸ K, dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x) = φ g
  have e := finsum_eq_single
    (fun x : G ⧸ K => dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x))
    ((1 : G) : G ⧸ K) (fun x hx => by
      show dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x) = 0
      rw [h1, if_neg (out_not_mem_of_ne_one K x hx), zero_smul])
  rw [e]
  have hm := out_mem_of_eq_one K ((1 : G) : G ⧸ K) rfl
  rw [h1, if_pos hm, one_smul]
  simp [AMF] at hφ
  have := hφ 1 Γ.one_mem g _ hm
  rw [one_mul, show (⟨1, Γ.one_mem⟩ : Γ) = 1 from rfl, map_one] at this
  simpa using this
end Formalism.UG.P
