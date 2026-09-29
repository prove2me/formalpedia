-- Prove2me | solution 1 for FullLevelTate.comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cbe7cba3-df06-5de3-a2f3-9db8bbc443d3

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem

set_option autoImplicit false

open scoped TensorProduct

namespace FullLevelTateLawA

variable (q : ℕ) [Fact q.Prime]

theorem det_diagOneElem (e : (ZMod q)ˣ) :
    Matrix.GeneralLinearGroup.det (ModularCurve.FullLevel.diagOneElem q e) = e := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, ModularCurve.FullLevel.coe_diagOneElem, Matrix.det_fin_two_of]
  ring

theorem diag_mem_hSubgroup {g : CuspidalType.GL2 q} {α : (GaloisField q 2)ˣ}
    (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q) :
    (ModularCurve.FullLevel.diagOneElem q (Matrix.GeneralLinearGroup.det g), α) ∈ DrinfeldCurve.hSubgroup q := by
  rw [DrinfeldCurve.mem_hSubgroup_iff] at hg ⊢
  rw [← hg]
  refine Units.ext ?_
  rw [DrinfeldCurve.coe_hChar_apply, DrinfeldCurve.coe_hChar_apply]
  congr 2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply, det_diagOneElem]

end FullLevelTateLawA

set_option maxHeartbeats 6400000 in
open FullLevelTateLawA in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (I : Type)
    (sp : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] I)
    (hlevel : ∀ h : DrinfeldCurve.hSubgroup q,
      ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 = 1) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
            (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp)
    (hinert : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ h : DrinfeldCurve.hSubgroup q,
      ι ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 : GaloisField q 2) =
          P.tameCharacter π τ →
        (∃ e : (ZMod q)ˣ, (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 =
          ModularCurve.FullLevel.diagOneElem q e) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
              (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
              ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
            DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g, α), hg⟩ ∘ₗ sp := by
  intro τ hτ α hα g hg

  set d : CuspidalType.GL2 q := ModularCurve.FullLevel.diagOneElem q (Matrix.GeneralLinearGroup.det g) with hd_def
  have hd : (d, α) ∈ DrinfeldCurve.hSubgroup q := diag_mem_hSubgroup q hg
  have hgd : (g * d⁻¹, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q := by
    have hmem := (DrinfeldCurve.hSubgroup q).mul_mem hg ((DrinfeldCurve.hSubgroup q).inv_mem hd)
    rwa [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at hmem

  have hL : sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam (g * d⁻¹)).baseChange ℚ_[lam] =
      DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g * d⁻¹, 1), hgd⟩ ∘ₗ sp :=
    hlevel ⟨(g * d⁻¹, 1), hgd⟩ rfl
  have hI : sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam d *
        ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
      DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(d, α), hd⟩ ∘ₗ sp :=
    hinert τ hτ ⟨(d, α), hd⟩ hα ⟨Matrix.GeneralLinearGroup.det g, rfl⟩

  have hsplit : ModularCurve.FullLevel.tateGL2 q M' lam g * ModularCurve.FullLevel.tateGal q M' lam τ =
      ModularCurve.FullLevel.tateGL2 q M' lam (g * d⁻¹) *
        (ModularCurve.FullLevel.tateGL2 q M' lam d * ModularCurve.FullLevel.tateGal q M' lam τ) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
  have hprod : (⟨(g * d⁻¹, 1), hgd⟩ : DrinfeldCurve.hSubgroup q) * ⟨(d, α), hd⟩ = ⟨(g, α), hg⟩ :=
    Subtype.ext (Prod.ext (inv_mul_cancel_right g d) (one_mul α))
  calc sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
          ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam]
      = sp ∘ₗ ((ModularCurve.FullLevel.tateGL2 q M' lam (g * d⁻¹)).baseChange ℚ_[lam] ∘ₗ
          (ModularCurve.FullLevel.tateGL2 q M' lam d *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam]) := by
        rw [hsplit, Module.End.mul_eq_comp, LinearMap.baseChange_comp]
    _ = (sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam (g * d⁻¹)).baseChange ℚ_[lam]) ∘ₗ
          (ModularCurve.FullLevel.tateGL2 q M' lam d *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] := by
        rw [LinearMap.comp_assoc]
    _ = (DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g * d⁻¹, 1), hgd⟩ ∘ₗ sp) ∘ₗ
          (ModularCurve.FullLevel.tateGL2 q M' lam d *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] := by rw [hL]
    _ = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g * d⁻¹, 1), hgd⟩ ∘ₗ
          (sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam d *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam]) := by
        rw [LinearMap.comp_assoc]
    _ = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g * d⁻¹, 1), hgd⟩ ∘ₗ
          (DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(d, α), hd⟩ ∘ₗ sp) := by rw [hI]
    _ = (DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g * d⁻¹, 1), hgd⟩ *
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(d, α), hd⟩) ∘ₗ sp := by
        rw [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g, α), hg⟩ ∘ₗ sp := by
        rw [← map_mul, hprod]

end S_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
end P2MW
export P2MW.S_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem (solution)
