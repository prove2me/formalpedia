-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.act_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:03.093033+00:00
-- url     : https://prove2.me/submissions/f1e75c09-263f-43d4-97e3-dc4adbed7db6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_psi_eq_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_col_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g : (Matrix (Fin n) (Fin n) L)ˣ)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (psiPath L isVec μ N I) =
      ∑ p ∈ F.pi (fun _ => (univ : Finset (Finset (Fin n)))),
        term isVec μ N F (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I
          (extF F p) := by
  rw [psi_eq_prod L hF hI, map_prod]
  simp_rw [col_act]
  rw [Finset.prod_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold term
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_attach F]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp [extF, x.2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
