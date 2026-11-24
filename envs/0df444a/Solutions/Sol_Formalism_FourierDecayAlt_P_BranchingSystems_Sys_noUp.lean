-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:20:44.755829+00:00
-- url     : https://prove2.me/submissions/b4e562ee-c345-422d-9d05-3c82582aa139

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_between
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_runUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}
namespace Formalism.FourierDecayAlt.P.BranchingSystems
namespace Sys
theorem _root_.solution (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.castSucc) :
    ¬ P (Function.update M i (M i + 1)) := by
  intro h0
  by_cases hz : (i : ℕ) = 0
  · have hall : ∀ t, M i + 1 ≤ t → P (Function.update M i t) := fun t ht =>
      runUp h.up M i _ h0 t ht (fun t' a _ j e => by
        have : L j ≤ L i.castSucc := h.anti.antitone (by rw [Fin.le_def]; simp [hz])
        omega)
    exact (Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i + 1 + (s : ℤ))
      (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)
  · let i' : Fin n := ⟨i - 1, by omega⟩
    have e1 : i'.succ = i.castSucc := by
      ext
      simp [i']
      omega
    have b1 := (hM i').1
    rw [e1, ← hi] at b1
    have h1 := runUp h.up M i _ h0 (M i') (by omega)
      (fun t' a b => between h.anti i' (by rw [e1]; omega) (by have := (hM i').2; omega))
    have hne : i' ≠ i := by
      intro e
      have := congrArg Fin.val e
      simp [i'] at this
      omega
    exact hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))
end Sys
end Formalism.FourierDecayAlt.P.BranchingSystems
