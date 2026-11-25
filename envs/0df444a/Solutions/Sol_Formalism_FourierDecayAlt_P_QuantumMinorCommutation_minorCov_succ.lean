-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:18.146538+00:00
-- url     : https://prove2.me/submissions/999605ea-9572-4871-940e-98e0c39b7862

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorCov_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_skip_one_eq_succAbove
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_skip_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_eps_sa
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_PI_QnCovHatW_skip_one_eq_succAbove
import Theorems.Thm_PI_QnZeroLevelWork_skip_one_eq_succAbove


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
namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
    (η : Fin (m + 2) → A) (hE : GlRel E) (hη : IsCov E η) (u : ℂ) (q p i : Fin (m + 2)) (hip : i ≠ p) :
    qminor (t := m + 1) E (skip1 q) (skip1 p) u * η i - η i * qminor (t := m + 1) E (skip1 q) (skip1 p) u =
      ∑ a : Fin (m + 2), if a = q then 0 else
        ((eps a q * eps i p * (-1) ^ ((a : ℕ) + (i : ℕ)) : ℤ) : A) *
          (qminor (t := m) E (skip2 (min a q) (max a q)) (skip2 (min i p) (max i p)) u * η a) := by
  obtain ⟨l₀, rfl⟩ := Fin.exists_succAbove_eq hip
  have h := minorCov_gen E hE η hη q.succAbove p.succAbove l₀
    (fun k => fun hk => Fin.succAbove_ne l₀ k (Fin.succAbove_right_injective hk)) u
  rw [skip_one_eq_succAbove, skip_one_eq_succAbove, h, Fin.sum_univ_succAbove _ q, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [if_neg (Fin.succAbove_ne q l), skip_comp, skip_comp]
  congr 2
  rw [pow_add, pow_add, ← eps_sa q l, ← eps_sa p l₀]
  ring
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
