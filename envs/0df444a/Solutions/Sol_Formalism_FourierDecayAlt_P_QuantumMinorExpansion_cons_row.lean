-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.cons_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:49.027852+00:00
-- url     : https://prove2.me/submissions/ab6b2bb2-afd9-454b-8a4d-8651ed3b2316

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_row_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution {N : ℕ} (a b : Fin (N + 1) → Fin n) (q c : Fin (N + 1)) (w : ℂ) :
    qminor E (bE (a c) (a ∘ q.succAbove)) b w =
      if c = q then ((-1 : ℤ) ^ (q : ℕ)) • qminor E a b w else 0 := by
  split_ifs with h
  · subst h
    have h1 : bE (a c) (a ∘ c.succAbove) = a ∘ (c.cycleRange.symm) := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp
      · simp
    rw [h1, quantumMinorRowSkew_holds A n (N + 1) E a b _ w, Equiv.Perm.sign_symm, Fin.sign_cycleRange, zsmul_eq_mul]
    simp
  · obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq h
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E _ b w 0 c'.succ (Fin.succ_ne_zero _).symm (by simp)
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
