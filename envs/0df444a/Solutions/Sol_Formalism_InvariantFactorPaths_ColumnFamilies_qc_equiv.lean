-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:09.346387+00:00
-- url     : https://prove2.me/submissions/5180fa17-26e2-431f-a61c-e2ffb65682a9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_isDomain
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_genPt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_genPt_int
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_li_field
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_two

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
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) :
    M.A * ph.map (Int.castRingHom _) = ph.map (Int.castRingHom _) * TMat mu := by
  have := qc_isDomain ℤ n
  let F := FractionRing (GLCoord ℤ n)
  let ψ : GLCoord ℤ n →+* GLCoord F n := (algebraMap F (GLCoord F n)).comp (algebraMap (GLCoord ℤ n) F)
  have hli := qc_li_field hA hS hmu hβ F
  ext i I
  have h := qc_two hβ ph hph (qc_genPt F n) (Matrix.GeneralLinearGroup.map ψ (qc_genPt ℤ n)) I
  rw [qc_evGL_genPt, qc_evGL_map, qc_evGL_genPt_int, RingHom.comp_id] at h
  have h' : ∑ j, (algebraMap (GLCoord ℤ n) F ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) -
      algebraMap (GLCoord ℤ n) F ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I)) • mapCoord (n := n) F (β j) = 0 := by
    simp only [Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h
  have h'' := Fintype.linearIndependent_iff.1 hli _ h' i
  exact IsFractionRing.injective (GLCoord ℤ n) F (sub_eq_zero.1 h'')
end Formalism.InvariantFactorPaths.ColumnFamilies
