-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellPrefixResidueSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:17.256975+00:00
-- url     : https://prove2.me/submissions/597a4092-7776-49fe-9530-5b1c57ca2fa9

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (M h : ℕ) (hhM : h ≤ M) (S : Finset (Fin (2 ^ h))) :
    (shellPrefixResidueSet M h hhM S).card = 2 ^ (M - h) * S.card := by
  classical
  let e : {n : ℕ // n ∈ dyadicShell M} ≃
      Fin (2 ^ (M - h)) × Fin (2 ^ h) :=
    dyadicShellPrefixEquiv M h hhM
  have hc :
      (shellPrefixResidueSet M h hhM S).card =
        ((Finset.univ : Finset (Fin (2 ^ (M - h)))).product S).card := by
    apply Finset.card_bij (fun n _hn => e n)
    · intro n hn
      have hnS := (Finset.mem_filter.mp hn).2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hnS⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      exact e.injective heq
    · intro b hb
      refine ⟨e.symm b, ?_, by simp [e]⟩
      simp only [shellPrefixResidueSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hbS : b.2 ∈ S := (Finset.mem_product.mp hb).2
      simpa [e] using hbS
  rw [hc]
  calc
    ((Finset.univ : Finset (Fin (2 ^ (M - h)))).product S).card =
        (Finset.univ : Finset (Fin (2 ^ (M - h)))).card * S.card :=
      Finset.card_product _ _
    _ = 2 ^ (M - h) * S.card := by simp
end FirstPassageLinearTransport
