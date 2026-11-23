-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.desc_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:14.673815+00:00
-- url     : https://prove2.me/submissions/2410594d-28d5-40d1-863a-f8e59b41efef

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {R P P' : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] (L S0 : Submodule R P) (L' S0' : Submodule R P')
    (Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0')) (hS : S0 ≤ L) (hS' : S0' ≤ L')
    (hrel : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → (x ∈ L ↔ y ∈ L')) :
    ∃ φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L'), ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  have hq' : S0' ≤ LinearMap.ker L'.mkQ := by rw [Submodule.ker_mkQ]; exact hS'
  have hq : S0 ≤ LinearMap.ker L.mkQ := by rw [Submodule.ker_mkQ]; exact hS
  let F : P →ₗ[R] P' ⧸ L' := (S0'.liftQ L'.mkQ hq').comp (Ψ.toLinearMap.comp S0.mkQ)
  let G : P' →ₗ[R] P ⧸ L := (S0.liftQ L.mkQ hq).comp (Ψ.symm.toLinearMap.comp S0'.mkQ)
  have hFv : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      F x = Submodule.Quotient.mk y := by
    intro x y h
    show (S0'.liftQ L'.mkQ hq') (Ψ (Submodule.Quotient.mk x)) = _
    rw [h]; rfl
  have hGv : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      G y = Submodule.Quotient.mk x := by
    intro x y h
    show (S0.liftQ L.mkQ hq) (Ψ.symm (Submodule.Quotient.mk y)) = _
    rw [← h, Ψ.symm_apply_apply]; rfl
  have hF : L ≤ LinearMap.ker F := by
    intro x hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk x))
    rw [LinearMap.mem_ker, hFv x y hy.symm, Submodule.Quotient.mk_eq_zero]
    exact (hrel x y hy.symm).1 hx
  have hG : L' ≤ LinearMap.ker G := by
    intro y hy
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.symm (Submodule.Quotient.mk y))
    have hxy : Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
      rw [hx, Ψ.apply_symm_apply]
    rw [LinearMap.mem_ker, hGv x y hxy, Submodule.Quotient.mk_eq_zero]
    exact (hrel x y hxy).2 hy
  let φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L') :=
    LinearEquiv.ofLinearMap (L.liftQ F hF) (L'.liftQ G hG)
      (by
        apply LinearMap.ext
        intro c
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.symm (Submodule.Quotient.mk y))
        have hxy : Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
          rw [hx, Ψ.apply_symm_apply]
        show (L.liftQ F hF) (G y) = Submodule.Quotient.mk y
        rw [hGv x y hxy]
        exact hFv x y hxy)
      (by
        apply LinearMap.ext
        intro c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk x))
        show (L'.liftQ G hG) (F x) = Submodule.Quotient.mk x
        rw [hFv x y hy.symm]
        exact hGv x y hy.symm)
  exact ⟨φ, fun x y h => hFv x y h⟩
end Formalism.FourierDecayAlt.P.A5x9
