-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:20:14.538168+00:00
-- url     : https://prove2.me/submissions/53966985-8186-40bd-81c9-49cd4e3a52dc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  have hrow : ∀ q : Fin (2 * r + k + 1), Hpk k r (esI k r b) q = if q = eI k r b then 1 else 0 := by
    intro q
    have e : q = eI k r b ↔ q.val = b.val := by rw [Fin.ext_iff]; simp only [eI]
    by_cases h1 : q = eI k r b
    · rw [if_pos h1]; have := e.mp h1
      unfold Hpk
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]; have := fun h => h1 (e.mpr h)
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨-, h2, -⟩; omega)]
  simp only [herm, bvec, dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul, hrow]
    simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
