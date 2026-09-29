-- Prove2me | solution 1 for DrinfeldCurve.coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/05d77fe4-4c20-54bb-8dab-5196a69cffa7

import Mathlib
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_DrinfeldCurve_exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField

set_option autoImplicit false

open DrinfeldCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (E : Type) [Field E] [Algebra κ E] (e : E ≃ₐ[κ] ↥(DrinfeldCurve.quotField q κ C)) (z : E)
    (hz : ∀ Q : AlgebraicCurve.Place κ E,
      (∀ (c : CoordRing q κ) (w : ↥(DrinfeldCurve.quotField q κ C)),
          (w : drinfeldFunctionField q κ) = algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) c →
          e.symm w ∈ Q.toValuationSubring) →
      z ∈ Q.toValuationSubring) :
    ((e z : ↥(DrinfeldCurve.quotField q κ C)) : drinfeldFunctionField q κ) ∈
      Set.range (algebraMap (CoordRing q κ) (drinfeldFunctionField q κ)) := by
  classical

  haveI hfin : Finite ↥(Subgroup.closure (Set.range fun ζ : ↥C =>
      hFunctionFieldAction q κ ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
        one_mem_hSubgroup_of_mem q ζ⟩)) := by
    let ψ : ↥C →* (drinfeldFunctionField q κ ≃ₐ[κ] drinfeldFunctionField q κ) :=
      { toFun := fun ζ => hFunctionFieldAction q κ ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
          one_mem_hSubgroup_of_mem q ζ⟩
        map_one' := by
          have : (⟨(1, (((1 : ↥C) : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)), one_mem_hSubgroup_of_mem q (1 : ↥C)⟩ : ↥(hSubgroup q)) = 1 :=
            Subtype.ext rfl
          rw [this, map_one]
        map_mul' := fun a b => by
          rw [← map_mul]
          congr 1
          exact Subtype.ext (Prod.ext (one_mul _).symm rfl) }
    have hrange : (Set.range fun ζ : ↥C =>
      hFunctionFieldAction q κ ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
        one_mem_hSubgroup_of_mem q ζ⟩) = (ψ.range : Set _) := by
      ext g; simp [ψ]
    rw [hrange, Subgroup.closure_eq]
    haveI : Finite ↥C := inferInstance
    exact Set.finite_range ψ |>.to_subtype
  have hint : ∀ f : drinfeldFunctionField q κ, IsIntegral ↥(DrinfeldCurve.quotField q κ C) f := fun f => FixedPoints.isIntegral _ _ f

  let φ : E →ₐ[κ] drinfeldFunctionField q κ := (DrinfeldCurve.quotField q κ C).val.comp (e : E →ₐ[κ] ↥(DrinfeldCurve.quotField q κ C))
  have hφe : ∀ t : E, φ t = ((e t : ↥(DrinfeldCurve.quotField q κ C)) : drinfeldFunctionField q κ) := fun t => rfl
  have h1 : ((e : E →ₐ[κ] ↥(DrinfeldCurve.quotField q κ C)) : E →+* ↥(DrinfeldCurve.quotField q κ C)).IsIntegral :=
    RingHom.isIntegral_of_surjective _ e.surjective
  have h2 : ((DrinfeldCurve.quotField q κ C).val : ↥(DrinfeldCurve.quotField q κ C) →+* drinfeldFunctionField q κ).IsIntegral := fun f => hint f
  have hφ : φ.toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2

  have hCv : ∀ v : AlgebraicCurve.Place κ (drinfeldFunctionField q κ),
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (x q κ) ∈ v.toValuationSubring →
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (y q κ) ∈ v.toValuationSubring →
      ∀ c : CoordRing q κ, algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) c ∈ v.toValuationSubring := by
    intro v hX hY c
    obtain ⟨p, rfl⟩ := DrinfeldCurve.mk_surjective q κ c
    induction p using MvPolynomial.induction_on with
    | C a =>
      have : DrinfeldCurve.mk q κ (MvPolynomial.C a) = algebraMap κ (CoordRing q κ) a := (DrinfeldCurve.mk q κ).commutes a
      rw [this, ← IsScalarTower.algebraMap_apply]
      exact v.algebraMap_mem' a
    | add p p' hp hp' => rw [map_add, map_add]; exact v.toValuationSubring.add_mem _ _ hp hp'
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      refine v.toValuationSubring.mul_mem _ _ hp ?_
      fin_cases i
      · exact hX
      · exact hY

  obtain ⟨b, -, hb⟩ := DrinfeldCurve.exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place q κ C
      ((e z : ↥(DrinfeldCurve.quotField q κ C)) : drinfeldFunctionField q κ) (e z).2 (by
    intro v hX hY
    have hQ := hz (v.restrictAlong φ hφ) (by
      intro c w hw
      show φ (e.symm w) ∈ v.toValuationSubring
      rw [hφe, AlgEquiv.apply_symm_apply, hw]
      exact hCv v hX hY c)
    have : φ z ∈ v.toValuationSubring := hQ
    rwa [hφe] at this)
  exact ⟨b, hb⟩

end S_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField
end P2MW
export P2MW.S_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField (solution)
