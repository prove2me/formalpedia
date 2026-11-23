-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_generic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:24.584824+00:00
-- url     : https://prove2.me/submissions/09557dad-adf9-4674-bda6-7e1747eaeaf1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_alg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] [Algebra R B] (bm gm : Matrix (Fin n) (Fin n) B)
    (hb : ∀ a c, a < c → bm a c = 0) (hbd : ∀ a, bm a a ≠ 0) (hg : gm.det ≠ 0)
    (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    aeval (fun v : Fin n × Fin n => (bm * gm) v.2 v.1) Q =
      (∏ a, bm a a ^ ν a) * aeval (fun v : Fin n × Fin n => gm v.2 v.1) Q := by
  let F := FractionRing B
  let φ : B →+* F := algebraMap B F
  have hinj : Function.Injective φ := IsFractionRing.injective B F
  have hbdet : (φ.mapMatrix bm).det ≠ 0 := by
    rw [← RingHom.map_det, Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij),
      map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hbd a
  have hgdet : (φ.mapMatrix gm).det ≠ 0 := by
    rw [← RingHom.map_det, map_ne_zero_iff _ hinj]; exact hg
  let b' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hbdet
  let g' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hgdet
  have hb' : b'.val = φ.mapMatrix bm := rfl
  have hg' : g'.val = φ.mapMatrix gm := rfl
  have h := hQ F b' g' (by intro a c hac; rw [hb']; show φ (bm a c) = 0; rw [hb a c hac, map_zero])
  have hev : ∀ (M : Matrix (Fin n) (Fin n) B) (h' : GL (Fin n) F), h'.val = φ.mapMatrix M →
      evGLR h' (algebraMap _ (GLCoord R n) (rename Prod.swap Q)) =
        φ (aeval (fun v : Fin n × Fin n => M v.2 v.1) Q) := by
    intro M h' hh
    rw [qh_evGLR_alg, coe_eval₂Hom, eval₂_rename, aeval_def, eval₂_comp_left, hh]
    rw [IsScalarTower.algebraMap_eq R B F]
    rfl
  rw [hev (bm * gm) (b' * g') (by rw [Units.val_mul, hb', hg', map_mul]), hev gm g' hg'] at h
  apply hinj
  rw [map_mul, map_prod]
  simp only [map_pow]
  simpa [hb'] using h
end Formalism.InvariantFactorPaths.ColumnFamilies
