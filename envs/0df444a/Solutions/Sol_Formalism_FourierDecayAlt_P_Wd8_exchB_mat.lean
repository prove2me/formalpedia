-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.exchB_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:48.0928+00:00
-- url     : https://prove2.me/submissions/f473e63f-1d9b-4ca7-9d0a-bb9a39127220

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exch_list_rev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_lift_reduction_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_list_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_cc_bT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sitesCommute_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_transfer_conjTranspose_commute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_lift_reduction_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
section Abstract
variable {R ι : Type} [Monoid R]
end Abstract
section Basic
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Basic
section Sites
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
private theorem lift0_conjT_prod_lemma (L : List (Site A)) (Y : K) :
    (lift0 ((L.map fun σ => Ts σ Y).prod)ᴴ : M2 (SlopeTestRemainingChoices S A)) =
      (L.reverse.map fun σ => lift0 (Ts σ Y)ᴴ).prod := by
  induction L with
  | nil => simp [liftMatrix_one]
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, lift_reduction_mul, ih,
      List.reverse_cons, List.map_append, List.prod_append]
    simp
end Sites
section Product
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Product
end Formalism.FourierDecayAlt.P.Wd8
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites,
      lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ)
    (h2 : sites.Pairwise SitesCommute) :
    lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * Xm w Y * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * Xm w Y * lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ := by
  have e := exch_list_rev (Xm w Y) (fun σ => (lift0 (Ts σ Y)ᴴ : M2 (SlopeTestRemainingChoices S A)))
    (fun σ => d0 (bT σ w)) sites h1 (h2.imp fun {σ τ} hst =>
      ⟨liftMatrix_transfer_conjTranspose_commute (cc_bT hst w) Y, liftMatrix_transfer_conjTranspose_commute (cc_bT (sitesCommute_symm hst) w) Y⟩)
  rw [lift0_conjT_prod_lemma, diagScalar_list_prod, List.map_map]
  exact e
end Formalism.FourierDecayAlt.P.Wd8
