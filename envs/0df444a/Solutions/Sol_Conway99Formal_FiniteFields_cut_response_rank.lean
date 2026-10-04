-- Prove2me | solution 1 for Conway99Formal.FiniteFields.cut_response_rank
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T00:19:25.009772+00:00
-- url     : https://prove2.me/submissions/0e236efb-ef56-4da8-9801-7ad088da8914

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix SimpleGraph Finset Module

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem sum_if_pair (x : V → ZMod 2) {i j : V} (hij : i ≠ j) :
    (∑ v : V, if v = i ∨ v = j then x v else 0) = x i + x j := by
  have hs (v : V) : (if v = i ∨ v = j then x v else 0) =
      (if v = i then x v else 0) + (if v = j then x v else 0) := by
    by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp

private theorem incidence_response_apply (x : V → ZMod 2) (i j : V) :
    (((H.incMatrix (ZMod 2))ᵀ).mulVec x) s(i, j) =
      if H.Adj i j then x i + x j else 0 := by
  classical
  by_cases hij : H.Adj i j
  · have hne := H.ne_of_adj hij
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      H.incMatrix_apply', H.mk'_mem_incidenceSet_iff, hij, true_and,
      if_true, ite_mul, one_mul, zero_mul]
    exact sum_if_pair x hne
  · simp [Matrix.mulVec, dotProduct, H.incMatrix_apply',
      H.mk'_mem_incidenceSet_iff, hij]

private theorem response_zero_iff_adj (x : V → ZMod 2) :
    ((H.incMatrix (ZMod 2))ᵀ).mulVec x = 0 ↔
      ∀ i j : V, H.Adj i j → x i = x j := by
  constructor
  · intro hx i j hij
    have he := congrFun hx s(i, j)
    rw [incidence_response_apply H x i j, if_pos hij] at he
    have he' : x i + x j = 0 := by simpa using he
    exact (add_eq_zero_iff_eq_neg.mp he').trans (ZMod.neg_eq_self_mod_two _)
  · intro hx
    funext e
    induction e using Sym2.ind with
    | h i j =>
      rw [incidence_response_apply]
      by_cases hij : H.Adj i j
      · rw [if_pos hij, hx i j hij]
        have htwo : (2 : ZMod 2) = 0 := by decide
        simpa [← two_mul, htwo]
      · simp [hij]

private theorem response_zero_iff_reachable (x : V → ZMod 2) :
    ((H.incMatrix (ZMod 2))ᵀ).mulVec x = 0 ↔
      ∀ i j : V, H.Reachable i j → x i = x j := by
  rw [response_zero_iff_adj]
  constructor
  · intro h i j ⟨w⟩
    induction w with
    | nil => rfl
    | cons hA _ h' => exact (h _ _ hA).trans h'
  · intro h i j hij
    exact h i j hij.reachable

private noncomputable def response_ker_basis_aux (c : H.ConnectedComponent) :
    LinearMap.ker ((H.incMatrix (ZMod 2))ᵀ).mulVecLin := by
  classical
  refine ⟨fun i => if H.connectedComponentMk i = c then 1 else 0, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, response_zero_iff_reachable]
  intro i j hr
  rw [SimpleGraph.ConnectedComponent.sound hr]

private theorem response_ker_basis_independent :
    LinearIndependent (ZMod 2) (response_ker_basis_aux H) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • response_ker_basis_aux H c =
      fun i => g (H.connectedComponentMk i) := by
    simp only [response_ker_basis_aux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [h] at h0
  intro c
  obtain ⟨i, hi⟩ : ∃ i : V, H.connectedComponentMk i = c := Quot.exists_rep c
  exact hi ▸ congrFun h0 i

set_option backward.isDefEq.respectTransparency.types false in
private theorem response_ker_basis_spans :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range (response_ker_basis_aux H)) := by
  classical
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hx : ∀ i j : V, H.Reachable i j → x.val i = x.val j :=
    (response_zero_iff_reachable H x.val).mp (by
      simpa only [Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp x.property))
  use Quot.lift x.val hx
  ext j
  simp only [response_ker_basis_aux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, ↓reduceIte]
  rfl

private noncomputable def response_ker_basis :
    Basis H.ConnectedComponent (ZMod 2)
      (LinearMap.ker ((H.incMatrix (ZMod 2))ᵀ).mulVecLin) :=
  Basis.mk (response_ker_basis_independent H) (response_ker_basis_spans H)

/-- The binary cut response has rank seven minus the number of components, including isolates. -/
theorem cut_response_rank (H : SimpleGraph (Fin 7)) [DecidableRel H.Adj] :
    (H.incMatrix (ZMod 2)).rank + Nat.card H.ConnectedComponent = 7 := by
  classical
  have hk : Module.finrank (ZMod 2)
      (LinearMap.ker ((H.incMatrix (ZMod 2))ᵀ).mulVecLin) =
      Fintype.card H.ConnectedComponent := by
    rw [Module.finrank_eq_card_basis (response_ker_basis H)]
  have hr := ((H.incMatrix (ZMod 2))ᵀ).mulVecLin.finrank_range_add_finrank_ker
  change ((H.incMatrix (ZMod 2))ᵀ).rank +
      Module.finrank (ZMod 2)
        (LinearMap.ker ((H.incMatrix (ZMod 2))ᵀ).mulVecLin) =
      Module.finrank (ZMod 2) (Fin 7 → ZMod 2) at hr
  rw [hk] at hr
  simpa [Matrix.rank_transpose, finrank_pi] using hr

#print axioms cut_response_rank

end Conway99Formal.FiniteFields

open Matrix

theorem solution (H : SimpleGraph (Fin 7)) [DecidableRel H.Adj] :
    (H.incMatrix (ZMod 2)).rank + Nat.card H.ConnectedComponent = 7 := by
  exact Conway99Formal.FiniteFields.cut_response_rank H

#print axioms solution
