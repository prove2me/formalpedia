-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.bracket_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:50.714989+00:00
-- url     : https://prove2.me/submissions/6fe11888-037b-43fa-9a52-27d122aef0d1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_nu_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_brkPol
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_of_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem
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
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) ∈ dualWeyl ℤ n n (qn_nu mu) := by
  rw [qn_T_brkPol]
  have h1 : qn_delta n ∈ dualWeyl ℤ n n (initW n n) :=
    initMinor_mem (R := ℤ) (fun p : Fin n => Fin.castLE (le_refl n) p) (le_refl n)
  refine dualWeyl_of_eq (dualWeyl_mul (dualWeyl_pow h1 (mu (lastIdx n)).toNat) (tableauBideterminant_mem_dualWeyl ℤ hmu I)) ?_
  rw [qn_nu_eq hmu]
  funext t
  simp [initW]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
