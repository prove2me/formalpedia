-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:17:39.35591+00:00
-- url     : https://prove2.me/submissions/6945fd47-36b6-4a48-8f3e-8c73209e36d9

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_between
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_runDown
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
theorem _root_.solution (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.succ + 1) :
    ¬ P (Function.update M i (M i - 1)) := by
  intro h0
  by_cases hz : (i : ℕ) + 1 = n
  · have hall : ∀ t, t ≤ M i - 1 → P (Function.update M i t) := fun t ht =>
      runDown h.down M i _ h0 t ht (fun t' _ b j e => by
        have : L i.succ ≤ L j := h.anti.antitone (by
          rw [Fin.le_def]
          have := j.2
          simp
          omega)
        omega)
    exact (Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i - 1 - (s : ℤ))
      (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)
  · let i' : Fin n := ⟨i + 1, by have := i.2; omega⟩
    have e1 : i'.castSucc = i.succ := by
      ext
      simp [i']
    have b1 := (hM i').2
    rw [e1] at b1
    have h1 := runDown h.down M i _ h0 (M i') (by omega)
      (fun t' a b => between h.anti i' (by have := (hM i').1; omega) (by rw [e1]; omega))
    have hne : i' ≠ i := by
      intro e
      have := congrArg Fin.val e
      simp [i'] at this
    exact hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))
end Sys
end Formalism.FourierDecayAlt.P.BranchingSystems
