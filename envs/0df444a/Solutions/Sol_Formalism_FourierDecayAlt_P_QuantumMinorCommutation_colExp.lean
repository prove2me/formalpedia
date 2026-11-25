-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.colExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:13.645733+00:00
-- url     : https://prove2.me/submissions/41ead447-d5fa-48d7-b80a-ad2ed476c291

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_sgn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_expansion_last_column
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_sign_cycleToLast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorCommutation
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation
theorem _root_.solution (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * Tm E (u - (m : ℂ)) (a l) (b l₀)) := by
  have h := quantumMinorColSkew_holds A n (m + 1) E hE a b (cycleToLast m l₀) u
  have hs : ((Equiv.Perm.sign (cycleToLast m l₀) : ℤˣ) : ℤ) = (-1) ^ (m - (l₀ : ℕ)) := by
    rw [sign_cycleToLast]
    simp
  rw [hs] at h
  have h2 : qminor E a b u = (((-1 : ℤ) ^ (m - (l₀ : ℕ)) : ℤ) : A) * qminor E a (b ∘ cycleToLast m l₀) u := by
    rw [h, ← mul_assoc, ← Int.cast_mul, ← pow_add, sgn_congr (b := 0) (by omega)]
    simp
  rw [h2, expansion_last_column A n m E a _ u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h0 : (b ∘ cycleToLast m l₀) (Fin.last m) = b l₀ := by
    simp [cycleToLast_last]
  have h1 : (b ∘ cycleToLast m l₀) ∘ Fin.castSucc = b ∘ l₀.succAbove := by
    funext k
    simp [cycleToLast_castSucc]
  have hl := l₀.isLt
  rw [h0, h1, ← mul_assoc, ← Int.cast_mul, ← pow_add,
    sgn_congr (a := m - (l₀ : ℕ) + (m + (l : ℕ))) (b := (l₀ : ℕ) + (l : ℕ)) (by omega)]
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
