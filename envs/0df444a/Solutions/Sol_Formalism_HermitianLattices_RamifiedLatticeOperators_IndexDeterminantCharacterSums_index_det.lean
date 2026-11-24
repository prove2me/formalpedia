-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.index_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.482848+00:00
-- url     : https://prove2.me/submissions/f9aa0114-2368-4c29-99d7-b1183d8b62e1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_lenQuotSpan
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_mulVecLin_inj
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_endo_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution (ϖ : R) (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n]
    (u : Matrix n n R) (hu : u.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det := by
  set L := u.mulVecLin with hL
  have hinj : Function.Injective L := mulVecLin_inj u hu
  have h : Module.finrank R (LinearMap.range L) = Module.finrank R (n → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun R n
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range L) b h).length_eq,
    Module.length_pi_of_fintype]
  rw [Finset.sum_congr rfl (fun i _ => lenQuotSpan ϖ hϖ _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)),
    ← Finset.emultiplicity_prod hϖ.prime]
  set a := Submodule.smithNormalFormCoeffs b h
  set b' := Submodule.smithNormalFormTopBasis b h
  set ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : n → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  let P : (n → R) →ₗ[R] (n → R) := b'.constr R (fun i => (ab i : n → R))
  have hPb : ∀ i, P (b' i) = a i • b' i := by
    intro i; simp only [P, Basis.constr_basis, hab]
  have hdetP : LinearMap.det P = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' P = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hPb, map_smul, b'.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.det_diagonal]
  have hPinj : Function.Injective P := endo_inj P (by
    rw [hdetP]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i))
  have hPL : ∀ x, P x ∈ LinearMap.range L := by
    intro x
    rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [map_smul, hPb, ← hab]
    exact Submodule.smul_mem _ _ (ab i).2
  have hLP : ∀ x, L x ∈ LinearMap.range P := by
    intro x
    let y : LinearMap.range L := ⟨L x, LinearMap.mem_range_self L x⟩
    refine ⟨∑ i, ab.repr y i • b' i, ?_⟩
    have e2 := congrArg Subtype.val (ab.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [map_sum]
    calc ∑ i, P (ab.repr y i • b' i) = ∑ i, ab.repr y i • (ab i : n → R) :=
          Finset.sum_congr rfl (fun i _ => by rw [map_smul, hPb, hab])
      _ = L x := e2
  let g : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective P hPinj).symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range P) hLP
  let g' : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective L hinj).symm.toLinearMap ∘ₗ P.codRestrict (LinearMap.range L) hPL
  have hg : P ∘ₗ g = L := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective P hPinj).apply_symm_apply
      (L.codRestrict (LinearMap.range P) hLP x))
  have hg' : L ∘ₗ g' = P := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective L hinj).apply_symm_apply
      (P.codRestrict (LinearMap.range L) hPL x))
  have hdetL : LinearMap.det L = u.det := by
    rw [hL, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  have d1 : LinearMap.det P ∣ u.det := ⟨LinearMap.det g, by rw [← hdetL, ← hg, LinearMap.det_comp]⟩
  have d2 : u.det ∣ LinearMap.det P := ⟨LinearMap.det g', by rw [← hdetL, ← hg', LinearMap.det_comp]⟩
  rw [← hdetP]
  exact emultiplicity_eq_of_associated_right (associated_of_dvd_dvd d1 d2)
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
