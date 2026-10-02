-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.prop_2_14_principal_submatrix_in_Linv
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T04:34:58.936985+00:00
-- url     : https://prove2.me/submissions/5e46d503-a01d-4c30-8380-22322c99bd48

import Definitions.Def_DiscreteConvex_CombinatorialB_CondCPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_MemLInv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_DiscreteConvex_CombinatorialB_theorem_2_12_nine_conditions_equivalent

set_option autoImplicit false
open scoped BigOperators

namespace QuadraticPrincipalProof
open DiscreteConvex.CombinatorialB
variable {V : Type*} [Fintype V] [DecidableEq V]

def extendZero (S : Finset V) (x : {v // v ∈ S} → ℝ) (v : V) : ℝ :=
  if h : v ∈ S then x ⟨v,h⟩ else 0

@[simp] lemma extendZero_coe (S : Finset V) (x : {v // v ∈ S} → ℝ)
    (v : {v // v ∈ S}) : extendZero S x v = x v := by
  simp [extendZero, v.property]

lemma colDot_submatrix (M : Matrix V V ℝ) (S : Finset V)
    (x : {v // v ∈ S} → ℝ) (i : {v // v ∈ S}) :
    ColDot (M.submatrix Subtype.val Subtype.val) x i =
      ColDot M (extendZero S x) i := by
  unfold ColDot Matrix.mulVec dotProduct
  apply Fintype.sum_of_injective (fun j : {v // v ∈ S} => j.val) Subtype.val_injective
  · intro j hj
    have hjS : j ∉ S := fun h => hj ⟨⟨j,h⟩,rfl⟩
    simp [extendZero,hjS]
  · intro j
    simp [Matrix.submatrix]

theorem condCPlus_submatrix (M : Matrix V V ℝ) (hM : CondCPlus M) (S : Finset V) :
    CondCPlus (M.submatrix ((↑) : {v // v ∈ S} → V) ((↑) : {v // v ∈ S} → V)) := by
  intro x i hi
  have hi' : i.val ∈ SuppPosR (extendZero S x) := by
    simpa [SuppPosR] using hi
  rcases hM (extendZero S x) i.val hi' with hp | ⟨j,hj,hij⟩
  · left
    simpa only [colDot_submatrix] using hp
  · have hjneg : extendZero S x j < 0 := by simpa [SuppNegR] using hj
    have hjS : j ∈ S := by
      by_contra hn
      simp [extendZero,hn] at hjneg
    refine Or.inr ⟨⟨j,hjS⟩,?_,?_⟩
    · simpa [SuppNegR,extendZero,hjS] using hjneg
    · simpa only [colDot_submatrix] using hij

lemma posDef_of_memLInv (M : Matrix V V ℝ) (hM : MemLInv M) : M.PosDef := by
  rcases hM with ⟨L,hLs,hLp,ho,hr,rfl⟩
  exact hLp.inv

lemma principal_posDef (M : Matrix V V ℝ) (hM : MemLInv M) (S : Finset V) :
    (M.submatrix ((↑) : {v // v ∈ S} → V) ((↑) : {v // v ∈ S} → V)).PosDef :=
  (posDef_of_memLInv M hM).submatrix Subtype.val_injective

end QuadraticPrincipalProof

#print axioms QuadraticPrincipalProof.condCPlus_submatrix
#print axioms QuadraticPrincipalProof.principal_posDef

set_option autoImplicit false

namespace QuadraticPrincipalProof
open DiscreteConvex.CombinatorialB

theorem principal_memLInv {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : MemLInv M) (S : Finset V) :
    MemLInv (M.submatrix ((↑) : {x // x ∈ S} → V) ((↑) : {x // x ∈ S} → V)) := by
  have hMpd := posDef_of_memLInv M hM
  have hMs : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp hMpd.isHermitian
  have hMd : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hMpd.isUnit).ne_zero
  have hC : CondCPlus M :=
    ((theorem_2_12_nine_conditions_equivalent M hMs hMd).out 0 4).mp hM
  let N := M.submatrix ((↑) : {x // x ∈ S} → V) ((↑) : {x // x ∈ S} → V)
  have hNpd : N.PosDef := principal_posDef M hM S
  have hNs : N.IsSymm := Matrix.isHermitian_iff_isSymm.mp hNpd.isHermitian
  have hNd : N.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det N).mp hNpd.isUnit).ne_zero
  exact ((theorem_2_12_nine_conditions_equivalent N hNs hNd).out 0 4).mpr
    (condCPlus_submatrix M hC S)

end QuadraticPrincipalProof

#print axioms QuadraticPrincipalProof.principal_memLInv

open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : MemLInv M) (S : Finset V) :
    MemLInv (M.submatrix ((↑) : {x // x ∈ S} → V) ((↑) : {x // x ∈ S} → V)) := by
  exact QuadraticPrincipalProof.principal_memLInv M hM S

#print axioms solution
