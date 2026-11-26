-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:24:41.560944+00:00
-- url     : https://prove2.me/submissions/d2ec54c0-422e-4bfa-b6a8-d61bdb4f69bb

import Definitions.Def_BipHamCount_Deterministic_Core
import Theorems.Thm_BipHamCount_Deterministic_lemma_3_1
open BipHamCount.Deterministic Finset Equiv Matrix
open scoped BigOperators Matrix

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

private lemma principal_det {V : Type*} [LinearOrder V]
    (M : Matrix V V ℤ) (U : Finset V) :
    minor M U U = (M.submatrix (↑) (↑) : Matrix U U ℤ).det := by
  classical
  rw [minor, dif_pos rfl]
  exact Matrix.det_submatrix_equiv_self (U.orderIsoOfFin rfl).toEquiv
    (M.submatrix (↑) (↑) : Matrix U U ℤ)

private lemma principal_perm {V : Type*} [LinearOrder V]
    (M : Matrix V V ℤ) (U : Finset V) :
    permMinor M U U = (M.submatrix (↑) (↑) : Matrix U U ℤ).permanent := by
  classical
  rw [permMinor, dif_pos rfl]
  let e := (U.orderIsoOfFin rfl).toEquiv
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro π
  apply Fintype.prod_equiv e
  intro i
  simp [Matrix.submatrix_apply, squareSub, Equiv.permCongr_apply, e]

private lemma perm_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix J J ℤ) (e : I ≃ J) : (M.submatrix e e).permanent = M.permanent := by
  classical
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro π
  apply Fintype.prod_equiv e
  intro i; simp [submatrix_apply, Equiv.permCongr_apply]

private lemma perm_diagBlock {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (C : Matrix I I ℤ) (D : Matrix J J ℤ) :
    (Matrix.fromBlocks C 0 0 D).permanent = C.permanent * D.permanent := by
  classical
  simp only [Matrix.permanent]
  rw [sum_mul_sum, ← sum_product', univ_product_univ]
  symm
  refine Fintype.sum_of_injective (Perm.sumCongrHom I J) Perm.sumCongrHom_injective _ _ ?_ ?_
  · intro π hn
    have hf : ¬ ∀ i : I, ∃ j : I, Sum.inl j = π (Sum.inl i) := by
      intro h
      apply hn
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨i,rfl⟩
      exact h i
    obtain ⟨i,hi⟩ := not_forall.mp hf
    obtain (⟨j,hj⟩ | ⟨j,hj⟩) : (∃ j : I, π (.inl i) = .inl j) ∨
        ∃ j : J, π (.inl i) = .inr j := by cases he : π (.inl i) <;> grind
    · exact (hi ⟨j,hj.symm⟩).elim
    · exact prod_eq_zero (mem_univ (.inl i)) (by simp [hj])
  · rintro ⟨σ,τ⟩
    simp [Fintype.prod_sum_type, Perm.sumCongrHom_apply]

private lemma switch_sign (d : ℕ) :
    (Perm.sign (Equiv.sumComm (Fin d) (Fin d)) : ℤ) = (-1 : ℤ)^d := by
  classical
  let σ := Equiv.sumComm (Fin d) (Fin d)
  have hp : σ ^ 2 = 1 := by ext (i|j) <;> rfl
  have : IsEmpty (Function.fixedPoints σ) := ⟨by
    rintro ⟨x,hx⟩; cases x <;> cases hx⟩
  rw [show Equiv.sumComm (Fin d) (Fin d) = σ from rfl, Perm.sign_of_pow_two_eq_one hp]
  simp [Fintype.card_sum]
  congr 1
  omega

private lemma perm_antiBlock {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    (Matrix.fromBlocks 0 A B 0).permanent = A.permanent * B.permanent := by
  let σ := Equiv.sumComm (Fin d) (Fin d)
  have hh : Matrix.fromBlocks 0 A B 0 = (Matrix.fromBlocks A 0 0 B).submatrix id σ := by
    ext (i|i) (j|j) <;> rfl
  rw [hh, Matrix.permanent_permute_rows, perm_diagBlock]

private lemma det_antiBlock {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    (Matrix.fromBlocks 0 A B 0).det = (-1 : ℤ)^d * (A.det * B.det) := by
  let σ := Equiv.sumComm (Fin d) (Fin d)
  have hh : Matrix.fromBlocks 0 A B 0 = (Matrix.fromBlocks A 0 0 B).submatrix id σ := by
    ext (i|i) (j|j) <;> rfl
  rw [hh, Matrix.det_permute', Matrix.det_fromBlocks_zero₂₁, switch_sign]
  norm_num

private lemma perm_unbalanced {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin a) ℤ)
    (hne : a ≠ b) : (Matrix.fromBlocks 0 A B 0).permanent = 0 := by
  classical
  apply sum_eq_zero
  intro π _
  by_contra h
  have hn (i : Fin a ⊕ Fin b) : Matrix.fromBlocks 0 A B 0 (π i) i ≠ 0 :=
    fun hi => h (prod_eq_zero (mem_univ i) hi)
  have hl (i : Fin a) : ∃ j : Fin b, π (.inl i) = .inr j := by
    cases hπ : π (.inl i) with
    | inl j => exact False.elim ((hn (.inl i)) (by simp [hπ]))
    | inr j => exact ⟨j,rfl⟩
  have hr (j : Fin b) : ∃ i : Fin a, π (.inr j) = .inl i := by
    cases hπ : π (.inr j) with
    | inl i => exact ⟨i,rfl⟩
    | inr i => exact False.elim ((hn (.inr j)) (by simp [hπ]))
  have il : Function.Injective (fun i => (hl i).choose) := by
    intro i j hij
    apply Sum.inl_injective (π.injective _)
    rw [(hl i).choose_spec,(hl j).choose_spec]
    exact congrArg Sum.inr hij
  have ir : Function.Injective (fun i => (hr i).choose) := by
    intro i j hij
    apply Sum.inr_injective (π.injective _)
    rw [(hr i).choose_spec,(hr j).choose_spec]
    exact congrArg Sum.inl hij
  have h₁ := Fintype.card_le_of_injective _ il
  have h₂ := Fintype.card_le_of_injective _ ir
  exact hne (by simpa using le_antisymm h₁ h₂)

private def enumSides {m a b : ℕ} (S T : Finset (Fin m)) (ha : S.card = a) (hb : T.card = b) :
    Fin a ⊕ Fin b ≃ S.disjSum T := by
  let l : S ≃ {i : Fin m // Sum.inl i ∈ S.disjSum T} := Equiv.subtypeEquivRight fun _ => inl_mem_disjSum.symm
  let r : T ≃ {i : Fin m // Sum.inr i ∈ S.disjSum T} := Equiv.subtypeEquivRight fun _ => inr_mem_disjSum.symm
  exact ((S.orderIsoOfFin ha).toEquiv.sumCongr (T.orderIsoOfFin hb).toEquiv).trans
    ((l.sumCongr r).trans (Equiv.subtypeSum (p := fun x => x ∈ S.disjSum T)).symm)

private lemma reindex_bip {m a b : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (S T : Finset (Fin m)) (ha : S.card = a) (hb : T.card = b) :
    (adjMatrix (bipDigraph A B)).submatrix (fun i => (enumSides S T ha hb i : Fin m ⊕ Fin m))
      (fun i => (enumSides S T ha hb i : Fin m ⊕ Fin m)) =
      Matrix.fromBlocks 0 (A.submatrix (S.orderEmbOfFin ha) (T.orderEmbOfFin hb))
          (B.submatrix (T.orderEmbOfFin hb) (S.orderEmbOfFin ha)) 0 := by
  ext (i|i) (j|j)
  · rfl
  · let x := S.orderEmbOfFin ha i
    let y := T.orderEmbOfFin hb j
    change (if decide (A x y = 1) then 1 else 0) = A x y
    rcases hA x y with h|h <;> simp [h]
  · let x := T.orderEmbOfFin hb i
    let y := S.orderEmbOfFin ha j
    change (if decide (B x y = 1) then 1 else 0) = B x y
    rcases hB x y with h|h <;> simp [h]
  · rfl

private lemma opm {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hs : S.card = d) (ht : T.card = d) :
    permMinor A S T = (A.submatrix (S.orderEmbOfFin hs) (T.orderEmbOfFin ht)).permanent := by
  subst d; rw [permMinor, dif_pos ht]; rfl

private lemma odm {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hs : S.card = d) (ht : T.card = d) :
    minor A S T = (A.submatrix (S.orderEmbOfFin hs) (T.orderEmbOfFin ht)).det := by
  subst d; rw [minor, dif_pos ht]; rfl

private abbrev sumOrd (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := by
  let o : LinearOrder (Fin m ⊕ Fin m) := LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective
  let de : DecidableEq (Fin m ⊕ Fin m) := inferInstance
  refine { o with toDecidableEq := de, compare_eq_compareOfLessAndEq := ?_ }
  intro x y
  have h : de = o.toDecidableEq := Subsingleton.elim _ _
  rw [h]
  exact o.compare_eq_compareOfLessAndEq x y

local instance (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := sumOrd m

private lemma cross_perm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (S T : Finset (Fin m)) :
    permMinor (adjMatrix (bipDigraph A B)) (S.disjSum T) (S.disjSum T) =
      if T.card = S.card then permMinor A S T * permMinor B T S else 0 := by
  classical
  let M := adjMatrix (bipDigraph A B)
  let C : Matrix (S.disjSum T) (S.disjSum T) ℤ := M.submatrix (↑) (↑)
  rw [principal_perm]
  by_cases h : T.card = S.card
  · rw [if_pos h, opm A S T rfl h, opm B T S h rfl]
    let e := enumSides S T rfl h
    have hh := reindex_bip A B hA hB S T rfl h
    exact ((perm_reindex C e).symm.trans (congrArg Matrix.permanent hh)).trans (perm_antiBlock _ _)
  · rw [if_neg h]
    let e := enumSides S T rfl rfl
    have hh := reindex_bip A B hA hB S T rfl rfl
    exact ((perm_reindex C e).symm.trans (congrArg Matrix.permanent hh)).trans (perm_unbalanced _ _ (Ne.symm h))

private lemma cross_det {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (S T : Finset (Fin m)) (h : T.card = S.card) :
    minor (adjMatrix (bipDigraph A B)) (S.disjSum T) (S.disjSum T) =
      (-1 : ℤ) ^ S.card * (minor A S T * minor B T S) := by
  classical
  rw [principal_det, odm A S T rfl h, odm B T S h rfl]
  let M := adjMatrix (bipDigraph A B)
  let C : Matrix (S.disjSum T) (S.disjSum T) ℤ := M.submatrix (↑) (↑)
  let e := enumSides S T rfl h
  have hh := reindex_bip A B hA hB S T rfl h
  exact ((Matrix.det_submatrix_equiv_self e C).symm.trans (congrArg Matrix.det hh)).trans (det_antiBlock _ _)

private lemma exv {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    (univ.erase v).powerset = univ.filter (fun s : Finset V => v ∉ s) := by
  ext S; simp [Finset.subset_erase]

private lemma split_sum {m : ℕ} (f : Finset (Fin m ⊕ Fin m) → ℤ) :
    ∑ U, f U = ∑ S : Finset (Fin m), ∑ T : Finset (Fin m), f (S.disjSum T) := by
  calc
    _ = ∑ st : Finset (Fin m) × Finset (Fin m), f (st.1.disjSum st.2) := by
      apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
      intro s; exact congrArg f s.toLeft_disjSum_toRight.symm
    _ = _ := Fintype.sum_prod_type _

theorem solution (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (v : Fin m) :
    sigma A B v = (hamCount (bipDigraph A B) : ℤ) := by
  classical
  have hl (i : Fin m ⊕ Fin m) : bipDigraph A B i i = false := by cases i <;> rfl
  refine Eq.trans ?_ ((lemma_3_1 (bipDigraph A B) hl (Sum.inl v)).symm.trans ?_)
  swap
  · apply congrArg (fun n : ℕ => (n : ℤ))
    exact congrArg (fun di => @hamCount (Fin m ⊕ Fin m) _ di (bipDigraph A B)) (Subsingleton.elim _ _)
  rw [exv, sum_filter, split_sum, sigma, exv, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  by_cases hv : v ∈ S
  · simp [hv]
  · rw [if_pos hv, powerset_univ, sum_filter]
    refine sum_congr rfl fun T _ => ?_
    have hcompl : (S.disjSum T)ᶜ = (Sᶜ).disjSum Tᶜ := by ext (u|u) <;> simp
    simp only [inl_mem_disjSum,hv,not_false_eq_true,if_true,cross_perm A B hA hB,hcompl,card_disjSum]
    by_cases h : T.card = S.card
    · have hh : Tᶜ.card = Sᶜ.card := by simp [Finset.card_compl,h]
      rw [if_pos h,cross_det A B hA hB Sᶜ Tᶜ hh, hh, sigmaTerm]
      have hs : (-1 : ℤ)^(Sᶜ.card + Sᶜ.card + 1) = -1 := by
        rw [show Sᶜ.card + Sᶜ.card + 1 = 2 * Sᶜ.card + 1 by omega, pow_succ, pow_mul]
        norm_num
      simp only [hs,if_pos h,pow_succ]
      ring
    · simp [h]

