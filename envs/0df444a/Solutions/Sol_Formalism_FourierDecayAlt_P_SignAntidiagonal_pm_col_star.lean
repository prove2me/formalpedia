-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pm_col_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:41.518324+00:00
-- url     : https://prove2.me/submissions/84aa1bdc-e3da-4dae-b370-033447d075e9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_NFOne_P_WS
import Theorems.Thm_NFOne_P_XS
import Theorems.Thm_NFOne_P_rowS
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [if_pos h1, if_pos (e.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
