-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:20.970801+00:00
-- url     : https://prove2.me/submissions/fbc216e5-4af4-4a5a-bf2f-78c5d23f6ec8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_rho_eq
import Theorems.Thm_Formalism_HC_Der_Rd_one_mem_KK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f ≤ 1 - (f.totient : ℝ) / N.totient := by
  open Classical in
  have one_le_card_inside_lemma_14 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      (1 : ℝ) ≤ (((KK N f).filter fun u => u ∈ U).card : ℝ) := by
    have h : 0 < ((KK N f).filter fun u => u ∈ U).card :=
      Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨one_mem_KK hf, one_mem U⟩⟩
    exact_mod_cast h
  rw [rho_eq U hf, mul_div_assoc]
  have hB := one_le_card_inside_lemma_14 U hf
  have h0 : (0 : ℝ) ≤ (f.totient : ℝ) / N.totient := by positivity
  nlinarith
end Formalism.HC.Der.Rd
