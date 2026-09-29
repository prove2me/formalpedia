-- Prove2me | solution 1 for DrinfeldCurve.algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1a6af3f1-b0b8-5afb-a55b-ac5e0c96caac

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField

set_option autoImplicit false

open DrinfeldCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    (∀ b : CoordRing q k,
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) b ∈ quotField q k C ↔
        ∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b = b) ∧
    (∀ z : drinfeldFunctionField q k, z ∈ quotField q k C →
      ∃ g h : CoordRing q k,
        (∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) g = g) ∧
        (∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) h = h) ∧
        h ≠ 0 ∧ z * algebraMap (CoordRing q k) (drinfeldFunctionField q k) h =
          algebraMap (CoordRing q k) (drinfeldFunctionField q k) g) := by
  classical

  set F := drinfeldFunctionField q k with hF
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  let gen : ↥C → (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) := fun ζ =>
    hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q ζ⟩
  have hquot : quotField q k C = IntermediateField.fixedField (Subgroup.closure (Set.range gen)) := rfl
  have hinj : Function.Injective (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) :=
    IsFractionRing.injective (CoordRing q k) (drinfeldFunctionField q k)

  have hgen : ∀ (ζ : ↥C) (b : CoordRing q k),
      gen ζ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) b) =
        algebraMap (CoordRing q k) (drinfeldFunctionField q k) (muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b) := by
    intro ζ b
    rw [show gen ζ = hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q (ζ : rootsOfUnity (q + 1) (GaloisField q 2))⟩ from rfl,
      hFunctionFieldAction_algebraMap, ← muAction_eq_hAction]

  have hmem : ∀ z : drinfeldFunctionField q k, z ∈ quotField q k C ↔ ∀ ζ : ↥C, gen ζ z = z := by
    intro z
    rw [hquot, IntermediateField.mem_fixedField_iff]
    constructor
    · intro h ζ; exact h (gen ζ) (Subgroup.subset_closure ⟨ζ, rfl⟩)
    · intro h f hf
      refine Subgroup.closure_induction (p := fun f _ => f z = z) ?_ ?_ ?_ ?_ hf
      · rintro f ⟨ζ, rfl⟩; exact h ζ
      · rfl
      · intro f g _ _ hf hg; rw [AlgEquiv.mul_apply, hg, hf]
      · intro f _ hf
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact hf.symm

  have part1 : ∀ b : CoordRing q k,
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) b ∈ quotField q k C ↔
        ∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b = b := by
    intro b
    rw [hmem]
    refine forall_congr' fun ζ => ?_
    rw [hgen]
    exact hinj.eq_iff
  refine ⟨part1, ?_⟩

  intro z hz
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k) z
  have hd0 : (d : CoordRing q k) ≠ 0 := nonZeroDivisors.ne_zero hd

  set hN : CoordRing q k := ∏ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) d with hhN
  set P : CoordRing q k := ∏ ζ ∈ (Finset.univ : Finset ↥C).erase 1, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) d with hP
  have hNeq : hN = d * P := by
    rw [hhN, hP, ← Finset.mul_prod_erase (Finset.univ : Finset ↥C) _ (Finset.mem_univ (1 : ↥C))]
    congr 1
    rw [OneMemClass.coe_one, map_one]; rfl
  have hNinv : ∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) hN = hN := by
    intro ζ
    rw [hhN, map_prod]
    simp_rw [← AlgEquiv.mul_apply, ← map_mul]
    exact Fintype.prod_equiv (Equiv.mulLeft ζ) _ _ (fun η => rfl)
  have hN0 : hN ≠ 0 := by
    rw [hhN, Finset.prod_ne_zero_iff]
    intro ζ _ h0
    exact hd0 ((muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2))).injective (by rw [h0, map_zero]))
  have hzN : algebraMap (CoordRing q k) (drinfeldFunctionField q k) a / algebraMap (CoordRing q k) (drinfeldFunctionField q k) d *
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) hN =
        algebraMap (CoordRing q k) (drinfeldFunctionField q k) (a * P) := by
    have hdne : algebraMap (CoordRing q k) (drinfeldFunctionField q k) d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    rw [hNeq, map_mul, map_mul, ← mul_assoc, div_mul_cancel₀ _ hdne]
  refine ⟨a * P, hN, ?_, hNinv, hN0, hzN⟩

  rw [← part1, ← hzN]
  exact mul_mem hz ((part1 hN).mpr hNinv)

end S_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
end P2MW
export P2MW.S_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField (solution)
