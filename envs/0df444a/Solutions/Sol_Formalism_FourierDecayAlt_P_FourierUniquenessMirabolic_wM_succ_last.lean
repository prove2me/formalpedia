-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_succ_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:32.636128+00:00
-- url     : https://prove2.me/submissions/07539558-fe3c-40ef-8b4d-662ec5d02514

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G
private lemma wMat_mul_apply_eq_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r c : Fin m) :
    (wMat m * M) r c = M r.rev c := by
  simp [wMat, Matrix.mul_apply]
private lemma wMat_mulVec_apply_eq_rev {m : ℕ} (v : Fin m → ℂ) (r : Fin m) : (wMat m *ᵥ v) r = v r.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]
private lemma finSumFinEquiv_symm_castSucc_eq_inl {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (Fin.castSucc i : Fin (n + 1)) = (Sum.inl i : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl
private lemma finSumFinEquiv_symm_last_eq_inr (n : ℕ) : finSumFinEquiv.symm (Fin.last n) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl
end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
theorem _root_.solution {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ (Fin.last n) = B i := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
