-- Prove2me | solution 1 for GaloisRepAdic.exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6bd3c723-233f-5029-bf37-324faff357a1

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ρA : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (hframe : ∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
      ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
        Matrix.dualNumberEquiv.symm
          ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
            LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
    (c : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) :
    ∃ φ : ρA.V ≃+ ρbar.V × ρbar.V,
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρA.V),
        φ (ρA.ρ (primeLocalToGlobal (pPrime p) σ) x) =
          ρbar.dualLiftModuleAct p
            (mapCocycles₁ (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) c) σ (φ x) := by
  classical
  obtain ⟨b, bbar, hmat⟩ := hframe

  let toPair : ρA.V → ρbar.V × ρbar.V := fun x =>
    (bbar.equivFun.symm (fun i => (b.equivFun x i).fst),
      bbar.equivFun.symm (fun i => (b.equivFun x i).snd))
  let ofPair : ρbar.V × ρbar.V → ρA.V := fun vw =>
    b.equivFun.symm (fun i => ((bbar.equivFun vw.1 i, bbar.equivFun vw.2 i) : DualNumber k))
  have hleft : ∀ x, ofPair (toPair x) = x := by
    intro x
    simp only [toPair, ofPair, LinearEquiv.apply_symm_apply]
    conv_rhs => rw [← b.equivFun.symm_apply_apply x]
    rfl
  have hright : ∀ vw, toPair (ofPair vw) = vw := by
    intro vw
    simp only [toPair, ofPair, LinearEquiv.apply_symm_apply, TrivSqZeroExt.fst_mk,
      TrivSqZeroExt.snd_mk, LinearEquiv.symm_apply_apply]
  let φ : ρA.V ≃+ ρbar.V × ρbar.V :=
    { toFun := toPair
      invFun := ofPair
      left_inv := hleft
      right_inv := hright
      map_add' := fun x y => by
        simp only [toPair, map_add, Pi.add_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          Prod.mk_add_mk]
        congr 1 <;> (rw [← map_add]; rfl) }
  refine ⟨φ, fun σ x => ?_⟩

  set g := primeLocalToGlobal (pPrime p) σ with hg

  set M₀ := LinearMap.toMatrix bbar bbar ((ρd g : DualNumber (Module.End k ρbar.V)).fst) with hM₀
  set M₁ := LinearMap.toMatrix bbar bbar ((ρd g : DualNumber (Module.End k ρbar.V)).snd) with hM₁

  have hcoord : b.equivFun (ρA.ρ g x) = Matrix.mulVec (LinearMap.toMatrix b b (ρA.ρ g)) (b.equivFun x) := by
    funext i
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b (ρA.ρ g) x]
    rfl
  rw [hmat g, ← hM₀, ← hM₁] at hcoord

  have hfst : ∀ i, (Matrix.mulVec (Matrix.dualNumberEquiv.symm ⟨M₀, M₁⟩) (b.equivFun x) i).fst =
      Matrix.mulVec M₀ (fun j => (b.equivFun x j).fst) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.dualNumberEquiv_symm_apply, Matrix.of_apply,
      TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk]
  have hsnd : ∀ i, (Matrix.mulVec (Matrix.dualNumberEquiv.symm ⟨M₀, M₁⟩) (b.equivFun x) i).snd =
      Matrix.mulVec M₀ (fun j => (b.equivFun x j).snd) i + Matrix.mulVec M₁ (fun j => (b.equivFun x j).fst) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.dualNumberEquiv_symm_apply, Matrix.of_apply,
      TrivSqZeroExt.snd_sum, DualNumber.snd_mul, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      ← Finset.sum_add_distrib]

  have hmv : ∀ (f : Module.End k ρbar.V) (a : Fin 2 → k),
      bbar.equivFun.symm (Matrix.mulVec (LinearMap.toMatrix bbar bbar f) a) = f (bbar.equivFun.symm a) := by
    intro f a
    apply bbar.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr bbar bbar f]
    congr 1
    ext j
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

  have hd' : ((ρd g : DualNumber (Module.End k ρbar.V)).fst) = ρbar.ρ g := by
    rw [hd g]; rfl
  have hsndop : ∀ v, ((ρd g : DualNumber (Module.End k ρbar.V)).snd) v =
      ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) g : Module.End k ρbar.V) (ρbar.ρ g v) := by
    intro v
    have h1 := hc g
    unfold groupCohomology.dualLiftToCochain at h1

    have h2 : ((c : _ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) g : Module.End k ρbar.V) *
        (↑(ρbar.ρ.toHomUnits g) : Module.End k ρbar.V) =
        ((ρd g : DualNumber (Module.End k ρbar.V)).snd) := by
      rw [h1, mul_assoc, Units.inv_mul, mul_one]
    have h3 := congrArg (fun (T : Module.End k ρbar.V) => T v) h2
    simp only [Module.End.mul_apply, MonoidHom.coe_toHomUnits] at h3
    exact h3.symm

  have hc' : ((mapCocycles₁ (primeLocalToGlobal (pPrime p))
      (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) c :
        primeLocalGaloisGroup (pPrime p) → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ :
          Module.End k ρbar.V) =
      ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) g : Module.End k ρbar.V) := by
    rfl

  show toPair (ρA.ρ g x) = ResidualGaloisRep.dualLiftModuleAct p ρbar _ σ (toPair x)
  simp only [toPair, ResidualGaloisRep.dualLiftModuleAct, hcoord]
  simp_rw [hfst, hsnd]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [hmv, hd']
  · dsimp only
    have hsplit : (fun i => Matrix.mulVec M₀ (fun j => (b.equivFun x j).snd) i +
        Matrix.mulVec M₁ (fun j => (b.equivFun x j).fst) i) =
        Matrix.mulVec M₀ (fun j => (b.equivFun x j).snd) +
          Matrix.mulVec M₁ (fun j => (b.equivFun x j).fst) := rfl
    rw [hsplit, map_add, hmv, hmv, hd', hsndop, hc', add_comm]

end S_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
end P2MW
export P2MW.S_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift (solution)
