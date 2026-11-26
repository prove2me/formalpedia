-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:17:46.104725+00:00
-- url     : https://prove2.me/submissions/a434a43e-8513-4774-bf6d-19008b52ab7e

import Definitions.Def_BipHamCount_Deterministic_Core
import Theorems.Thm_BipHamCount_Deterministic_lemma_2_3
open BipHamCount.Deterministic Finset Equiv Matrix
open scoped BigOperators Matrix

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

private lemma det_row {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℤ) :
    M.det = ∑ π : Perm V, (Perm.sign π : ℤ) * ∏ i, M i (π i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  rfl

private lemma perm_row {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℤ) :
    M.permanent = ∑ π : Perm V, ∏ i, M i (π i) := by
  rw [← Matrix.permanent_transpose M]
  rfl

private lemma permEntry {V : Type*} [DecidableEq V] (π : Perm V) (i j : V) :
    π.permMatrix ℤ i j = if π i = j then 1 else 0 := by
  simp [Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

private lemma entry_product {V : Type*} [Fintype V] [LinearOrder V]
    (π : Perm V) (U : Finset V) (τ : Perm U) :
    (∏ i : U, π.permMatrix ℤ i (τ i)) =
      if (∀ i : U, π (↑i) = (τ i : V)) then 1 else 0 := by
  classical
  by_cases h : ∀ i : U, π (↑i) = (τ i : V)
  · simp [permEntry,h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [if_neg h]
    exact prod_eq_zero (mem_univ i) (by simp [permEntry, hi])

private lemma permMinorDet {V : Type*} [Fintype V] [LinearOrder V]
    (π : Perm V) (U : Finset V) :
    minor (π.permMatrix ℤ) U U =
      ∑ τ : Perm U, if (∀ i : U, π (↑i) = (τ i : V))
        then (Perm.sign τ : ℤ) else 0 := by
  rw [principal_det, det_row]
  refine sum_congr rfl fun τ hτ => ?_
  change (Perm.sign τ : ℤ) * (∏ i : U, π.permMatrix ℤ i (τ i)) = _
  rw [entry_product]
  split <;> simp

private abbrev offV {V : Type*} [DecidableEq V] (v : V) := fun i : V => if i = v then (0 : ℤ) else 1
private noncomputable def cycleMatrix {V : Type*} [DecidableEq V] (v : V) (π : Perm V) : Matrix V V ℤ :=
  Matrix.diagonal (offV v) - π.permMatrix ℤ

private lemma det_cycleMatrix_zero {V : Type*} [Fintype V] [LinearOrder V]
    (v b : V) (π : Perm V) (h : ¬ π.SameCycle b v) : (cycleMatrix v π).det = 0 := by
  classical
  let f := fun i : V => if π.SameCycle b i then (1 : ℤ) else 0
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := f) (i := b)
  · rw [cycleMatrix, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, sub_eq_zero]
    ext i
    by_cases hi : i = v
    · subst i
      simp [Matrix.mulVec_diagonal, offV, f, h, Function.comp_apply, Equiv.Perm.sameCycle_apply_right]
    · simp [Matrix.mulVec_diagonal, offV, f, hi, Function.comp_apply, Equiv.Perm.sameCycle_apply_right]
  · simp [f, Perm.SameCycle.refl]

private lemma minor_perm_zero {V : Type*} [Fintype V] [LinearOrder V]
    (π : Perm V) (v : V) (ht : ∀ j, π.SameCycle v j)
    (U : Finset V) (hv : v ∈ U) (hu : U ≠ univ) : minor (π.permMatrix ℤ) U U = 0 := by
  classical
  rw [permMinorDet]
  apply sum_eq_zero
  intro τ _
  apply if_neg
  intro ha
  have step (i : V) (hi : i ∈ U) : π i ∈ U := by
    rw [ha ⟨i,hi⟩]; exact (τ ⟨i,hi⟩).property
  have hp (n : ℕ) : (π ^ n) v ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa [pow_succ', Perm.mul_apply] using step _ ih
  apply hu
  apply eq_univ_of_forall
  intro i
  obtain ⟨n,_,hn⟩ := (ht i).exists_pow_eq'
  exact hn ▸ hp n

private lemma minor_negative {V : Type*} [LinearOrder V] (M : Matrix V V ℤ) (U : Finset V) :
    minor (-M) U U = (-1 : ℤ) ^ U.card * minor M U U := by
  rw [principal_det, principal_det]
  change (-(M.submatrix (↑) (↑) : Matrix U U ℤ)).det = _
  simp [Matrix.det_neg]

private lemma minor_univ {V : Type*} [Fintype V] [LinearOrder V] (M : Matrix V V ℤ) :
    minor M univ univ = M.det := by
  classical
  rw [principal_det]
  let e : (univ : Finset V) ≃ V :=
    Equiv.ofBijective (fun x => ↑x) ⟨Subtype.val_injective, fun v => ⟨⟨v,mem_univ v⟩,rfl⟩⟩
  exact Matrix.det_submatrix_equiv_self e M

private lemma det_cycleMatrix_of_full {V : Type*} [Fintype V] [LinearOrder V]
    (v : V) (π : Perm V) (hc : π.IsCycle) (hf : π.support = univ) :
    (cycleMatrix v π).det = -1 := by
  classical
  have hn (i : V) : π i ≠ i := Perm.mem_support.mp (hf ▸ mem_univ i)
  have htrans (i : V) : π.SameCycle v i := hc.sameCycle (hn v) (hn i)
  rw [cycleMatrix, sub_eq_add_neg, lemma_2_3 (-(π.permMatrix ℤ)) (offV v)]
  rw [sum_eq_single (univ : Finset V)]
  · rw [minor_negative, minor_univ, Matrix.det_permutation, hc.sign, hf]
    simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one, Finset.compl_univ,
      Finset.prod_empty, mul_one]
    have hu : ∀ n : ℕ, ((-1:ℤ)^n)*((-1:ℤ)^n) = 1 := by
      intro n; rw [← mul_pow]; norm_num
    change (-1:ℤ)^(univ : Finset V).card * -((-1:ℤ)^(univ : Finset V).card) = -1
    rw [mul_neg, hu]
  · intro U _ hne
    by_cases hv : v ∈ U
    · rw [minor_negative, minor_perm_zero π v htrans U hv hne]; ring
    · have h0 : ∏ i ∈ Uᶜ, offV v i = 0 :=
        prod_eq_zero (mem_compl.mpr hv) (by simp [offV])
      rw [h0,mul_zero]
  · simp

private lemma det_outside {V : Type*} [Fintype V] [LinearOrder V] (M : Matrix V V ℤ)
    (S : Finset V) :
    minor M Sᶜ Sᶜ = (M.submatrix (↑) (↑) : Matrix {i // i ∉ S} {i // i ∉ S} ℤ).det := by
  classical
  rw [principal_det]
  let e : (Sᶜ : Finset V) ≃ {i : V // i ∉ S} :=
    Equiv.subtypeEquivRight (fun i => mem_compl)
  exact Matrix.det_submatrix_equiv_self e
    (M.submatrix (↑) (↑) : Matrix {i // i ∉ S} {i // i ∉ S} ℤ)

private lemma permDet_outside {V : Type*} [Fintype V] [LinearOrder V]
    (π : Perm V) (S : Finset V) :
    minor (π.permMatrix ℤ) Sᶜ Sᶜ = ∑ τ : Perm {i // i ∉ S},
      if (∀ j : {i // i ∉ S}, π ↑j = (τ j : V)) then (Perm.sign τ : ℤ) else 0 := by
  classical
  rw [det_outside, det_row]
  refine sum_congr rfl fun τ _ => ?_
  by_cases h : ∀ j : {i // i ∉ S}, π ↑j = (τ j : V)
  · simp [submatrix_apply,permEntry,h]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    rw [if_neg h]
    have hz : (∏ i : {u // u ∉ S}, π.permMatrix ℤ i (τ i)) = 0 :=
      prod_eq_zero (mem_univ j) (by simp [permEntry,hj])
    change (Perm.sign τ : ℤ) * (∏ i : {u // u ∉ S}, π.permMatrix ℤ i (τ i)) = 0
    rw [hz,mul_zero]

private def weight {V : Type*} [Fintype V] (M : Matrix V V ℤ) (π : Perm V) :=
  ∏ i, M i (π i)

private lemma sum_extensions {V : Type*} [Fintype V] [LinearOrder V] (M : Matrix V V ℤ)
    (S : Finset V) (τ : Perm {i // i ∉ S}) :
    (∑ π : Perm V, if (∀ j : {i // i ∉ S}, π ↑j = (τ j : V)) then weight M π else 0) =
      (M.submatrix (↑) (↑) : Matrix S S ℤ).permanent * ∏ j : {i // i ∉ S}, M j (τ j) := by
  classical
  rw [perm_row, sum_mul]
  symm
  refine Fintype.sum_of_injective (fun σ : Perm S => σ.subtypeCongr τ) ?_ _ _ ?_ ?_
  · intro σ ρ h
    apply Equiv.ext
    intro i
    simpa using Equiv.congr_fun h (i : V)
  · intro π hπ
    apply if_neg
    intro hτ
    have hmem (i : V) : π i ∈ S ↔ i ∈ S := by
      constructor
      · intro hpi
        by_contra hi
        exact (τ ⟨i,hi⟩).property (hτ ⟨i,hi⟩ ▸ hpi)
      · intro hi
        by_contra hpi
        let j : {i // i ∉ S} := τ.symm ⟨π i,hpi⟩
        have hj : π (j : V) = π i := by simpa [j] using hτ j
        exact j.property (by simpa only [π.injective hj] using hi)
    apply hπ
    refine ⟨π.subtypePerm hmem,?_⟩
    ext i
    by_cases hi : i ∈ S
    · rw [Perm.subtypeCongr.left_apply _ _ hi]; rfl
    · rw [Perm.subtypeCongr.right_apply _ _ hi]; exact (hτ ⟨i,hi⟩).symm
  · intro σ
    have ht (j : {i // i ∉ S}) : (σ.subtypeCongr τ) (↑j) = (τ j : V) := by simp
    rw [if_pos ht, weight, ← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
    simp [submatrix_apply]
    left
    exact Finset.prod_congr (by ext i; simp) (fun _ _ => rfl)

private lemma hamSliceProduct {V : Type*} [Fintype V] [LinearOrder V] (M : Matrix V V ℤ)
    (S : Finset V) :
    permMinor M S S * minor M Sᶜ Sᶜ =
      ∑ π : Perm V, weight M π * minor (π.permMatrix ℤ) Sᶜ Sᶜ := by
  classical
  rw [det_outside, det_row, principal_perm]
  simp_rw [permDet_outside, Finset.mul_sum]
  rw [sum_comm (s := (univ : Finset (Perm V)))]
  refine sum_congr rfl fun τ _ => ?_
  rw [← mul_assoc, mul_comm _ (Perm.sign τ : ℤ), mul_assoc]
  simp only [submatrix_apply]
  rw [← sum_extensions M S τ]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro π _
  by_cases hp : ∀ j : {i // i ∉ S}, π (↑j) = (τ j : V)
  · simp [hp, mul_comm]
  · simp [hp, mul_comm]

private lemma coeff_sum {V : Type*} [Fintype V] [LinearOrder V] (π : Perm V) (v : V) :
    (∑ U ∈ (univ.erase v).powerset,
        (-1 : ℤ) ^ (Uᶜ.card + 1) * minor (π.permMatrix ℤ) Uᶜ Uᶜ) =
      -(cycleMatrix v π).det := by
  classical
  have hdom : (univ.erase v).powerset = univ.filter (fun s : Finset V => v ∉ s) := by
    ext s
    simp [Finset.subset_erase]
  rw [cycleMatrix, sub_eq_add_neg, lemma_2_3 (-(π.permMatrix ℤ)) (offV v), powerset_univ,
    ← sum_neg_distrib, hdom, sum_filter]
  let e : Finset V ≃ Finset V := ⟨(·ᶜ), (·ᶜ), compl_compl, compl_compl⟩
  apply Fintype.sum_equiv e
  intro U
  change (if v ∉ U then _ else 0) =
    -(minor (-(π.permMatrix ℤ)) Uᶜ Uᶜ * ∏ i ∈ Uᶜᶜ, offV v i)
  rw [compl_compl,minor_negative]
  by_cases hv : v ∈ U
  · have hz : ∏ i ∈ U, offV v i = 0 := prod_eq_zero hv (by simp [offV])
    simp [hv,hz]
  · have ho : ∏ i ∈ U, offV v i = 1 := by
      apply Finset.prod_eq_one
      intro i hi; have hn : i ≠ v := fun h => hv (h ▸ hi); simp [offV,hn]
    simp [hv,ho,pow_succ]

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (adj : V → V → Bool) (hloop : ∀ u, adj u u = false) (v : V) :
    (hamCount adj : ℤ) =
      ∑ U ∈ (Finset.univ.erase v).powerset,
        (-1 : ℤ) ^ (Uᶜ.card + 1) * permMinor (adjMatrix adj) U U *
          minor (adjMatrix adj) Uᶜ Uᶜ := by
  classical
  let hamilton := fun π : Perm V =>
     π.IsCycle ∧ π.support = univ ∧ ∀ u, adj u (π u) = true
  have hcnt : (hamCount adj : ℤ) =
      ∑ π : Perm V, if hamilton π then (1:ℤ) else 0 := by
    simp [hamCount,hamilton]
  rw [hcnt]
  calc
    _ = ∑ π : Perm V, weight (adjMatrix adj) π * -(cycleMatrix v π).det := by
      apply sum_congr rfl
      intro π _
      by_cases ha : ∀ i, adj i (π i) = true
      · have hw : weight (adjMatrix adj) π = 1 := by simp [weight,adjMatrix,ha]
        have hn (i : V) : π i ≠ i := by
          intro he; have := ha i; rw [he,hloop] at this; contradiction
        have hs : π.support = univ := eq_univ_of_forall (fun i => Perm.mem_support.mpr (hn i))
        by_cases hc : π.IsCycle
        · simp [hamilton,hw,hs,ha,hc,det_cycleMatrix_of_full v π hc hs]
        · have nall : ¬ ∀ i, π.SameCycle v i := fun ht => hc ⟨v,hn v,fun {i} _ => ht i⟩
          obtain ⟨i,hi⟩ := not_forall.mp nall
          have hh : ¬ π.SameCycle i v := fun h => hi h.symm
          simp [hamilton,hw,hc,det_cycleMatrix_zero v i π hh]
      · obtain ⟨i,hi⟩ := not_forall.mp ha
        have hw : weight (adjMatrix adj) π = 0 :=
          prod_eq_zero (mem_univ i) (by simp [adjMatrix,hi])
        simp [hamilton,ha,hw]
    _ = _ := by
      simp_rw [← coeff_sum, Finset.mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun U _ => ?_
      rw [mul_assoc, hamSliceProduct (adjMatrix adj) U, Finset.mul_sum]
      refine sum_congr rfl fun π _ => ?_
      ring
