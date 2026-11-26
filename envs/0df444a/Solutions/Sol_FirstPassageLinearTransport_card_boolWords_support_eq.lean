-- Prove2me | solution 1 for FirstPassageLinearTransport.card_boolWords_support_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:23.935031+00:00
-- url     : https://prove2.me/submissions/c0a22d84-26e7-41eb-840f-394310a70dd9

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
theorem _root_.solution (n k : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun v => (boolSupport v).card = k)).card = n.choose k := by
  classical
  let e :
      {v : Fin n → Bool // (boolSupport v).card = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    (boolWordFinsetEquiv n).subtypeEquiv (fun _ => Iff.rfl)
  have hc := Fintype.card_congr e
  have hfinsets :
      ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun s => s.card = k)) =
        (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext s
    simp [Finset.mem_powersetCard]
  simpa [Fintype.card_subtype, hfinsets, Finset.card_powersetCard] using hc
end FirstPassageLinearTransport
