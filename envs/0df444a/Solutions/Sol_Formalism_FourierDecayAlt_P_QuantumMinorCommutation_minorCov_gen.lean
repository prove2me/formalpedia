-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:43.191038+00:00
-- url     : https://prove2.me/submissions/ed5e307d-bed2-4d9a-b27a-2747d7913316

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_Tm_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_commute_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_colExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (hE : GlRel E) (η : Fin n → A) (hη : IsCov E η) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, b (l₀.succAbove k) ≠ b l₀) (u : ℂ) :
    qminor E a b u * η (b l₀) - η (b l₀) * qminor E a b u =
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * η (a l)) := by
  rw [colExp E hE a b l₀ u, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (η (b l₀)) (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u) := by
    refine commute_qminor E _ _ u _ (fun s s' => ?_)
    have := hη ((a ∘ l.succAbove) s) ((b ∘ l₀.succAbove) s') (b l₀)
    rw [if_neg (show (b ∘ l₀.succAbove) s' ≠ b l₀ from hne s'), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E (u - (m : ℂ)) (a l) (b l₀) * η (b l₀) - η (b l₀) * Tm E (u - (m : ℂ)) (a l) (b l₀) = η (a l) := by
    rw [Tm_comm, hη, if_pos rfl]
  have hc : η (b l₀) * (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) =
      (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) * η (b l₀) := (Int.commute_cast _ _).eq
  rw [← mul_assoc (η (b l₀)), hc, mul_assoc _ (η (b l₀)), ← mul_assoc (η (b l₀)), hM.eq,
    mul_assoc _ _ (η (b l₀)), mul_assoc _ _ (η (b l₀)), mul_assoc _ (η (b l₀)), ← mul_sub, ← mul_sub, hT]
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
