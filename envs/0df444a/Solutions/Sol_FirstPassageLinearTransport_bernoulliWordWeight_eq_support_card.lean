-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliWordWeight_eq_support_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:36.795647+00:00
-- url     : https://prove2.me/submissions/679300c6-5c42-4ac9-a9de-0163ec753afb

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} {r : ℕ} (v : Fin r → Bool) :
    bernoulliWordWeight p v =
      p ^ (boolSupport v).card *
        (1 - p) ^ (r - (boolSupport v).card) := by
  classical
  unfold bernoulliWordWeight boolSupport
  rw [show (∏ i : Fin r, if v i then p else 1 - p) =
      ∏ i ∈ (Finset.univ : Finset (Fin r)),
        if v i = true then p else 1 - p by simp]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r))) (fun i => v i = true)
  have huniv : (Finset.univ : Finset (Fin r)).card = r := by simp
  rw [huniv] at hcard
  have hfalse :
      ((Finset.univ : Finset (Fin r)).filter
        (fun i => ¬v i = true)).card =
        r - ((Finset.univ : Finset (Fin r)).filter
          (fun i => v i = true)).card := by
    omega
  rw [hfalse]
end FirstPassageLinearTransport
