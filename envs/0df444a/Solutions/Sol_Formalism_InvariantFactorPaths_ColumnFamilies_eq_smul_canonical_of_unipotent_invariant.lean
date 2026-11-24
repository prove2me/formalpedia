-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.eq_smul_canonical_of_unipotent_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:44.258796+00:00
-- url     : https://prove2.me/submissions/11ee03b8-d605-4252-b70c-ec69a74545e4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_nu_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_P
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_span_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_trans_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_trans_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_raise
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_canonical_eq_smul_highestWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (f : GLCoord ℚ n)
    (hf : f ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)))
    (hinv : ∀ (R' : Type) [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
      (∀ a b, b < a → u.val a b = 0) → evGLR (R := ℚ) (x * u) f = evGLR (R := ℚ) x f) :
    ∃ c : ℚ, f = c • mapCoord ℚ (brk mu (canT mu)) := by
  obtain ⟨P, hP, rfl⟩ := qd_span_le mu hf
  obtain ⟨c, hc⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) P hP (by
    intro a b hab k hk
    unfold rowDiv
    rw [qd_raise mu P a b hab.ne (hinv _ _ _ (qd_trans_diag a b hab.ne _) (qd_trans_low a b hab _)),
      Polynomial.coeff_C, if_neg (by omega)])
  obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
  refine ⟨c / c0, ?_⟩
  rw [← qd_L_P, ← map_smul, h0, hc, smul_smul, div_mul_cancel₀ _ hc0]
end Formalism.InvariantFactorPaths.ColumnFamilies
