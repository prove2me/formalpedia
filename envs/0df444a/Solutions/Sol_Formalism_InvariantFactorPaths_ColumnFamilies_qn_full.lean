-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:22.655131+00:00
-- url     : https://prove2.me/submissions/91ead6be-9c7d-44f2-9b46-642be5ec944b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (J : Fin n → Fin n) :
    ∃ ε : ℤ, initMinor ℤ J (le_refl n) = ε • qn_delta n := by
  classical
  set M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.of fun p q : Fin n => X (Fin.castLE (le_refl n) p, Fin.castLE (le_refl n) q) with hM
  have h1 : initMinor ℤ J (le_refl n) = (M.submatrix J id).det := rfl
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤˣ) : ℤ), ?_⟩
    have h2 := Matrix.det_permute (Equiv.ofBijective J hb) M
    rw [h1]
    have h3 : M.submatrix J id = M.submatrix (Equiv.ofBijective J hb) id := rfl
    rw [h3, h2, zsmul_eq_mul]
    simp [qn_delta, lpMinor, hM]
  · refine ⟨0, ?_⟩
    rw [zero_smul, h1]
    unfold Function.Injective at hJ
    push Not at hJ
    obtain ⟨p, p', hpp, hne⟩ := hJ
    exact Matrix.det_zero_of_row_eq hne (by funext q; simp [Matrix.submatrix, hpp])
end Formalism.InvariantFactorPaths.ColumnFamilies
