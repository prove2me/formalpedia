-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.mixed_matrix_rank_max_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:08:14.835985+00:00
-- url     : https://prove2.me/submissions/6eab3c48-4df1-4831-973c-ad6da06d024c

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Definitions.Def_DiscreteConvex_MixedMatrices_IsNonsingularSub



namespace DiscreteConvex.MixedMatrices

open Matrix

def colmixNS {R C α : Type*} [DecidableEq C] (S : Finset C) (X Y : Matrix R C α) : Matrix R C α :=
  Matrix.of fun i j => if j ∈ S then X i j else Y i j

def rowmixNS {R C α : Type*} [DecidableEq R] (S : Finset R) (X Y : Matrix R C α) : Matrix R C α :=
  Matrix.of fun i j => if i ∈ S then X i j else Y i j

theorem det_add_colmixNS {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (X Y : Matrix n n α) : (X + Y).det = ∑ S : Finset n, (colmixNS S X Y).det := by
  simp only [Matrix.det_apply, colmixNS, Matrix.of_apply, Matrix.add_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_add, ← Finset.smul_sum, Finset.powerset_univ]
  congr 1
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext i; simp
  · congr 1; ext i; simp

theorem det_add_rowmixNS {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (X Y : Matrix n n α) : (X + Y).det = ∑ S : Finset n, (rowmixNS S X Y).det := by
  rw [← Matrix.det_transpose, Matrix.transpose_add, det_add_colmixNS]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Matrix.det_transpose (rowmixNS S X Y)]
  congr 1

theorem det_add_colmixNS' {R C α : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    [CommRing α] (e : R ≃ C) (X Y : Matrix R C α) :
    ((X + Y).submatrix id e).det = ∑ S : Finset C, ((colmixNS S X Y).submatrix id e).det := by
  rw [show (X + Y).submatrix id e = X.submatrix id e + Y.submatrix id e from rfl,
    det_add_colmixNS]
  refine Fintype.sum_equiv (Equiv.finsetCongr e) _ _ (fun S => ?_)
  congr 1
  ext i k
  simp [colmixNS, Equiv.finsetCongr_apply]

theorem rank_add_le_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K]
    (A B : Matrix R C K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_le_sub_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K] [DecidableEq R]
    [DecidableEq C] (M : Matrix R C K) (I : Finset R) (J : Finset C)
    (h : ∀ i j, M i j ≠ 0 → i ∈ I ∧ j ∈ J) :
    M.rank ≤ (M.submatrix ((↑) : I → R) ((↑) : J → C)).rank := by
  let B : Matrix R I K := Matrix.of fun i a => if (a : R) = i then 1 else 0
  let B' : Matrix J C K := Matrix.of fun b j => if (b : C) = j then 1 else 0
  have hM : B * M.submatrix ((↑) : I → R) ((↑) : J → C) * B' = M := by
    ext i j
    simp only [B, B', Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply]
    by_cases hi : i ∈ I
    · by_cases hj : j ∈ J
      · rw [Fintype.sum_eq_single (⟨j, hj⟩ : J)]
        · rw [if_pos rfl, mul_one, Fintype.sum_eq_single (⟨i, hi⟩ : I)]
          · simp
          · intro a ha; rw [if_neg (fun he => ha (Subtype.ext he)), zero_mul]
        · intro b hb; rw [if_neg (fun he => hb (Subtype.ext he)), mul_zero]
      · have : M i j = 0 := by by_contra hne; exact hj (h i j hne).2
        rw [this]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [if_neg (fun (he : (b : C) = j) => hj (he ▸ b.2)), mul_zero]
    · have : M i j = 0 := by by_contra hne; exact hi (h i j hne).1
      rw [this]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [Finset.sum_eq_zero (fun a _ => ?_), zero_mul]
      rw [if_neg (fun (he : (a : R) = i) => hi (he ▸ a.2)), zero_mul]
  calc M.rank = (B * M.submatrix ((↑) : I → R) ((↑) : J → C) * B').rank := by rw [hM]
    _ ≤ (B * M.submatrix ((↑) : I → R) ((↑) : J → C)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ _ := Matrix.rank_mul_le_right _ _

theorem mulVec_inj_of_rank_NS {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (M : Matrix m n K) (h : M.rank = Fintype.card n) (v : n → K) (hv : M *ᵥ v = 0) : v = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Module.finrank K (LinearMap.ker M.mulVecLin) = 0 := by
    unfold Matrix.rank at h; omega
  rw [Submodule.finrank_eq_zero] at h2
  have : v ∈ LinearMap.ker M.mulVecLin := by simpa using hv
  rw [h2] at this
  simpa using this

theorem det_ne_zero_of_rank_NS {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (M : Matrix n n K) (h : M.rank = Fintype.card n) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hd
  exact hv0 (mulVec_inj_of_rank_NS M h v hv)

theorem rank_full_iff_det_NS {a b K : Type*} [Fintype a] [Fintype b] [DecidableEq a] [Field K]
    (M : Matrix a b K) (e : a ≃ b) : M.rank = Fintype.card a ↔ (M.submatrix id e).det ≠ 0 := by
  have hr : (M.submatrix id e).rank = M.rank := by
    simpa using Matrix.rank_submatrix M (Equiv.refl a) e
  constructor
  · intro h; exact det_ne_zero_of_rank_NS _ (hr.trans h)
  · intro h; rw [← hr]; exact Matrix.rank_of_det_ne_zero h


theorem rank_map_full_NS {a b K F : Type*} [Fintype a] [Fintype b] [DecidableEq a] [Field K]
    [Field F] [Algebra K F] (Q : Matrix a b K) (hc : Fintype.card a = Fintype.card b)
    (h : (Q.map (algebraMap K F)).rank = Fintype.card a) : Q.rank = Fintype.card a := by
  let e := Fintype.equivOfCardEq hc
  rw [rank_full_iff_det_NS _ e] at h ⊢
  intro h0
  apply h
  have := RingHom.map_det (algebraMap K F) (Q.submatrix id e)
  rw [h0, map_zero] at this
  rw [this]; rfl

theorem forward_NS {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C] (Q : Matrix R C K) (T : Matrix R C F)
    (e : R ≃ C) (hd : ((Q.map (algebraMap K F) + T).submatrix id e).det ≠ 0) :
    ∃ I : Finset R, ∃ J : Finset C, IsNonsingularSub Q I J ∧ IsNonsingularSub T Iᶜ Jᶜ := by
  set Qf := Q.map (algebraMap K F) with hQf
  rw [det_add_colmixNS'] at hd
  obtain ⟨J, -, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have hsplit : colmixNS J Qf T = colmixNS J Qf 0 + colmixNS J 0 T := by
    ext i j; simp only [colmixNS, Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
    split_ifs <;> simp
  rw [hsplit, show (colmixNS J Qf 0 + colmixNS J 0 T).submatrix id e =
    (colmixNS J Qf 0).submatrix id e + (colmixNS J 0 T).submatrix id e from rfl,
    det_add_rowmixNS] at hJ
  obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
  set N : Matrix R C F := rowmixNS I (colmixNS J Qf 0) (colmixNS J 0 T) with hN
  have hNe : rowmixNS I ((colmixNS J Qf 0).submatrix id e) ((colmixNS J 0 T).submatrix id e)
      = N.submatrix id e := rfl
  rw [hNe] at hI
  have hrank : N.rank = Fintype.card R := (rank_full_iff_det_NS N e).2 hI
  set N1 : Matrix R C F := rowmixNS I (colmixNS J Qf 0) 0 with hN1
  set N2 : Matrix R C F := rowmixNS I 0 (colmixNS J 0 T) with hN2
  have hN12 : N = N1 + N2 := by
    ext i j; simp only [hN, hN1, hN2, rowmixNS, Matrix.of_apply, Matrix.add_apply,
      Matrix.zero_apply]
    split_ifs <;> simp
  have h1 : N1.rank ≤ (Qf.submatrix ((↑) : I → R) ((↑) : J → C)).rank := by
    have := rank_le_sub_NS N1 I J (fun i j hij => by
      simp only [hN1, rowmixNS, colmixNS, Matrix.of_apply, Matrix.zero_apply] at hij
      split_ifs at hij with h1 h2 <;> simp_all)
    convert this using 2
    ext a b; simp [hN1, rowmixNS, colmixNS, a.2, b.2]
  have h2 : N2.rank ≤ (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C)).rank := by
    have := rank_le_sub_NS N2 Iᶜ Jᶜ (fun i j hij => by
      simp only [hN2, rowmixNS, colmixNS, Matrix.of_apply, Matrix.zero_apply] at hij
      split_ifs at hij with h1 h2 <;> simp_all)
    convert this using 2
    ext a b
    have ha := a.2; have hb := b.2
    rw [Finset.mem_compl] at ha hb
    simp [hN2, rowmixNS, colmixNS, ha, hb]
  have hsum := rank_add_le_NS N1 N2
  rw [← hN12, hrank] at hsum
  have a1 := Matrix.rank_le_card_height (Qf.submatrix ((↑) : I → R) ((↑) : J → C))
  have a2 := Matrix.rank_le_card_width (Qf.submatrix ((↑) : I → R) ((↑) : J → C))
  have b1 := Matrix.rank_le_card_height
    (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C))
  have b2 := Matrix.rank_le_card_width
    (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C))
  simp only [Fintype.card_coe, Finset.card_compl] at a1 a2 b1 b2
  have hRC : Fintype.card R = Fintype.card C := Fintype.card_congr e
  have hIR : I.card ≤ Fintype.card R := Finset.card_le_univ I
  have hJC : J.card ≤ Fintype.card C := Finset.card_le_univ J
  have hIJ : I.card = J.card := by omega
  refine ⟨I, J, ⟨hIJ, ?_⟩, ⟨by rw [Finset.card_compl, Finset.card_compl]; omega, ?_⟩⟩
  · unfold MatrixSubRank
    have := rank_map_full_NS (F := F) (Q.submatrix ((↑) : I → R) ((↑) : J → C))
      (by simp [hIJ]) (by
        have : (Q.submatrix ((↑) : I → R) ((↑) : J → C)).map (algebraMap K F) =
          Qf.submatrix ((↑) : I → R) ((↑) : J → C) := rfl
        rw [this, Fintype.card_coe]; omega)
    rw [this, Fintype.card_coe]
  · unfold MatrixSubRank
    rw [Finset.card_compl]; omega


/-- the key nonsingular matrix: columns `J` from `Q`, other columns from the partial
permutation matrix of `π`. -/
theorem key_det_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K] [DecidableEq R]
    [DecidableEq C] (Q : Matrix R C K) (e : R ≃ C) (I : Finset R) (J : Finset C)
    (π : (Iᶜ : Finset R) ≃ (Jᶜ : Finset C))
    (hQinj : ∀ w : J → K, (Q.submatrix ((↑) : I → R) ((↑) : J → C)) *ᵥ w = 0 → w = 0)
    (P : Matrix R C K)
    (hP : ∀ i j, P i j = if h : i ∉ I then (if j = (π ⟨i, Finset.mem_compl.2 h⟩ : C) then 1 else 0)
      else 0) :
    ((colmixNS J Q P).submatrix id e).det ≠ 0 := by
  intro hd
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hd
  apply hw0
  set u : C → K := fun j => w (e.symm j) with hu
  have hrow : ∀ i, ∑ j, colmixNS J Q P i j * u j = 0 := by
    intro i
    have := congrFun hw i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Pi.zero_apply] at this
    rw [← this]
    refine (Fintype.sum_equiv e _ _ (fun k => ?_)).symm
    simp [hu]
  have huJ : ∀ j ∈ J, u j = 0 := by
    have := hQinj (fun b => u b) (by
      funext a
      have h := hrow a
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
      rw [← h]
      have hPa : ∀ j, P a j = 0 := fun j => by rw [hP]; simp [a.2]
      simp only [colmixNS, Matrix.of_apply, hPa, ite_mul, zero_mul]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact (Finset.sum_coe_sort J (fun j => Q a j * u j)))
    intro j hj
    exact congrFun this ⟨j, hj⟩
  have huJc : ∀ i : (Iᶜ : Finset R), u (π i) = 0 := by
    intro i
    have h := hrow i
    rw [← h]
    have hi : (i : R) ∉ I := Finset.mem_compl.1 i.2
    rw [Finset.sum_eq_single ((π i : C))]
    · have hnot : ((π i : C)) ∉ J := Finset.mem_compl.1 (π i).2
      simp only [colmixNS, Matrix.of_apply, if_neg hnot, hP, dif_pos hi]
      simp
    · intro j _ hj
      by_cases hjJ : j ∈ J
      · rw [huJ j hjJ, mul_zero]
      · simp only [colmixNS, Matrix.of_apply, if_neg hjJ, hP, dif_pos hi]
        rw [if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hu0 : u = 0 := by
    funext j
    by_cases hj : j ∈ J
    · exact huJ j hj
    · have := huJc (π.symm ⟨j, Finset.mem_compl.2 hj⟩)
      simpa using this
  funext k
  have := congrFun hu0 (e k)
  simpa [hu] using this


open Polynomial in
theorem poly_det_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K] [DecidableEq R]
    [DecidableEq C] (Q : Matrix R C K) (e : R ≃ C) (I : Finset R) (J : Finset C)
    (π : (Iᶜ : Finset R) ≃ (Jᶜ : Finset C))
    (hQinj : ∀ w : J → K, (Q.submatrix ((↑) : I → R) ((↑) : J → C)) *ᵥ w = 0 → w = 0)
    (P : Matrix R C K)
    (hP : ∀ i j, P i j = if h : i ∉ I then (if j = (π ⟨i, Finset.mem_compl.2 h⟩ : C) then 1 else 0)
      else 0) :
    ((Q.map Polynomial.C + Matrix.of fun i j => (Polynomial.X : K[X]) * Polynomial.C (P i j)).submatrix
      id e).det ≠ 0 := by
  rw [det_add_colmixNS']
  have hterm : ∀ S : Finset C, ((colmixNS S (Q.map Polynomial.C)
      (Matrix.of fun i j => (Polynomial.X : K[X]) * Polynomial.C (P i j))).submatrix id e).det =
      Polynomial.C ((colmixNS S Q P).submatrix id e).det *
        X ^ (Finset.univ.filter (fun k => e k ∉ S)).card := by
    intro S
    have hM : (colmixNS S (Q.map Polynomial.C)
      (Matrix.of fun i j => (Polynomial.X : K[X]) * Polynomial.C (P i j))).submatrix id e =
        Matrix.of fun i k => (fun k => if e k ∈ S then (1 : K[X]) else X) k *
          (((colmixNS S Q P).submatrix id e).map Polynomial.C) i k := by
      ext i k : 1
      simp only [colmixNS, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, id]
      split_ifs <;> simp
    rw [hM, Matrix.det_mul_row, show (((colmixNS S Q P).submatrix id e).map Polynomial.C).det =
      Polynomial.C ((colmixNS S Q P).submatrix id e).det from (RingHom.map_det _ _).symm, mul_comm]
    congr 1
    rw [Finset.prod_ite]
    simp
  simp_rw [hterm]
  intro h0
  have hc := congrArg (fun p => Polynomial.coeff p (Finset.univ.filter (fun k => e k ∉ J)).card) h0
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single J] at hc
  · rw [if_pos rfl] at hc
    exact key_det_NS Q e I J π hQinj P hP hc
  · intro S _ hSJ
    split_ifs with hcard
    · by_contra hd
      -- column zero argument: J ⊆ S
      have hJS : J ⊆ S := by
        intro j hj
        by_contra hjS
        apply hd
        apply Matrix.det_eq_zero_of_column_eq_zero (e.symm j)
        intro i
        simp only [Matrix.submatrix_apply, id, colmixNS, Matrix.of_apply, Equiv.apply_symm_apply,
          if_neg hjS, hP]
        by_cases h1 : i ∉ I
        · rw [dif_pos h1, if_neg]
          intro h2
          have h3 := (π ⟨i, Finset.mem_compl.2 h1⟩).2
          rw [← h2, Finset.mem_compl] at h3
          exact h3 hj
        · rw [dif_neg h1]
      apply hSJ
      have hsub : Finset.univ.filter (fun k => e k ∉ S) ⊆ Finset.univ.filter (fun k => e k ∉ J) := by
        intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h hk => h (hJS hk)
      have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      ext j
      have := congrArg (fun s => e.symm j ∈ s) heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply,
        eq_iff_iff] at this
      tauto
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h


theorem backward_NS {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C] (Q : Matrix R C K) (T : Matrix R C F)
    (e : R ≃ C)
    (hT : AlgebraicIndependent K (fun x : {p : R × C // T p.1 p.2 ≠ 0} => T x.1.1 x.1.2))
    (I : Finset R) (J : Finset C) (hQ : IsNonsingularSub Q I J)
    (hT' : IsNonsingularSub T Iᶜ Jᶜ) :
    ((Q.map (algebraMap K F) + T).submatrix id e).det ≠ 0 := by
  classical
  have hcard : Fintype.card (Iᶜ : Finset R) = Fintype.card (Jᶜ : Finset C) := by
    simp only [Fintype.card_coe]; exact hT'.1
  let e2 := Fintype.equivOfCardEq hcard
  have hdet2 := (rank_full_iff_det_NS (T.submatrix ((↑) : (Iᶜ : Finset R) → R)
    ((↑) : (Jᶜ : Finset C) → C)) e2).1 (by rw [Fintype.card_coe]; exact hT'.2)
  rw [Matrix.det_apply] at hdet2
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet2
  have hprod : ∏ k, T (σ k) (e2 k) ≠ 0 := by
    intro h; apply hσ
    simp only [Matrix.submatrix_apply, id] at h ⊢
    rw [h, smul_zero]
  have hall : ∀ k, T (σ k) (e2 k) ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.1 hprod) k (Finset.mem_univ _)
  let π : (Iᶜ : Finset R) ≃ (Jᶜ : Finset C) := σ.symm.trans e2
  have hπ : ∀ i : (Iᶜ : Finset R), T i (π i) ≠ 0 := by
    intro i
    have := hall (σ.symm i)
    simpa [π] using this
  have hQinj : ∀ w : J → K, (Q.submatrix ((↑) : I → R) ((↑) : J → C)) *ᵥ w = 0 → w = 0 :=
    mulVec_inj_of_rank_NS _ (by rw [Fintype.card_coe, ← hQ.1]; exact hQ.2)
  let P : Matrix R C K := Matrix.of fun i j =>
    if h : i ∉ I then (if j = (π ⟨i, Finset.mem_compl.2 h⟩ : C) then 1 else 0) else 0
  have hpoly := poly_det_NS Q e I J π hQinj P (fun i j => rfl)
  let G : Matrix R C (MvPolynomial {p : R × C // T p.1 p.2 ≠ 0} K) := Matrix.of fun i j =>
    MvPolynomial.C (Q i j) + (if h : T i j ≠ 0 then MvPolynomial.X ⟨(i, j), h⟩ else 0)
  let y : {p : R × C // T p.1 p.2 ≠ 0} → Polynomial K := fun x =>
    if h : x.1.1 ∉ I then (if x.1.2 = (π ⟨x.1.1, Finset.mem_compl.2 h⟩ : C) then Polynomial.X
      else 0) else 0
  have hφ : G.map (MvPolynomial.aeval y) =
      Q.map Polynomial.C + Matrix.of fun i j => (Polynomial.X : Polynomial K) * Polynomial.C (P i j) := by
    ext i j : 1
    simp only [G, P, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, map_add,
      MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
    congr 1
    by_cases hT0 : T i j ≠ 0
    · rw [dif_pos hT0, MvPolynomial.aeval_X]
      simp only [y]
      split_ifs <;> simp
    · rw [dif_neg hT0, map_zero]
      by_cases h1 : i ∉ I
      · rw [dif_pos h1, if_neg, Polynomial.C_0, mul_zero]
        intro h2; apply hT0; rw [h2]; exact hπ ⟨i, Finset.mem_compl.2 h1⟩
      · rw [dif_neg h1, Polynomial.C_0, mul_zero]
  have hgen : (G.submatrix id e).det ≠ 0 := by
    intro h0
    apply hpoly
    rw [← hφ]
    have := RingHom.map_det (MvPolynomial.aeval y).toRingHom (G.submatrix id e)
    rw [h0, map_zero] at this
    rw [this]; rfl
  have hA : G.map (MvPolynomial.aeval (fun x : {p : R × C // T p.1 p.2 ≠ 0} => T x.1.1 x.1.2)) =
      Q.map (algebraMap K F) + T := by
    ext i j : 1
    simp only [G, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, map_add,
      MvPolynomial.aeval_C]
    congr 1
    by_cases hT0 : T i j ≠ 0
    · rw [dif_pos hT0, MvPolynomial.aeval_X]
    · rw [dif_neg hT0, map_zero]; exact (not_not.1 hT0).symm
  intro h0
  apply hgen
  apply hT.eq_zero_of_aeval_eq_zero
  have := RingHom.map_det
    (MvPolynomial.aeval (fun x : {p : R × C // T p.1 p.2 ≠ 0} => T x.1.1 x.1.2)).toRingHom
    (G.submatrix id e)
  have h1 : (MvPolynomial.aeval (fun x : {p : R × C // T p.1 p.2 ≠ 0} => T x.1.1 x.1.2)).toRingHom.mapMatrix
      (G.submatrix id e) = (Q.map (algebraMap K F) + T).submatrix id e := by rw [← hA]; rfl
  rw [h1, h0] at this
  exact this

theorem nonsingular_iff_core {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T)
    (hsq : Fintype.card R = Fintype.card C) :
    IsNonsingularSub A (Finset.univ : Finset R) (Finset.univ : Finset C) ↔
      ∃ I : Finset R, ∃ J : Finset C, IsNonsingularSub Q I J ∧ IsNonsingularSub T Iᶜ Jᶜ := by
  let e := Fintype.equivOfCardEq hsq
  have hAeq : A = Q.map (algebraMap K F) + T := by
    ext i j; rw [hA.1 i j]; rfl
  have hsub : MatrixSubRank A Finset.univ Finset.univ = A.rank := by
    unfold MatrixSubRank
    exact Matrix.rank_submatrix A (Equiv.subtypeUnivEquiv Finset.mem_univ)
      (Equiv.subtypeUnivEquiv Finset.mem_univ)
  have hiff : IsNonsingularSub A (Finset.univ : Finset R) (Finset.univ : Finset C) ↔
      ((Q.map (algebraMap K F) + T).submatrix id e).det ≠ 0 := by
    rw [← rank_full_iff_det_NS _ e, ← hAeq]
    unfold IsNonsingularSub
    rw [hsub, Finset.card_univ, Finset.card_univ]
    exact ⟨fun h => h.2, fun h => ⟨hsq, h⟩⟩
  rw [hiff]
  constructor
  · exact forward_NS Q T e
  · rintro ⟨I, J, hQ, hT⟩
    exact backward_NS Q T e hA.2 I J hQ hT


theorem exists_rows_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K] [DecidableEq R]
    (M : Matrix R C K) :
    ∃ I : Finset R, I.card = M.rank ∧ (M.submatrix ((↑) : I → R) id).rank = M.rank := by
  obtain ⟨b, -, -, hspan, hli⟩ := exists_linearIndepOn_extension (K := K) (v := M.row)
    (s := (∅ : Set R)) (t := Set.univ) (by simp) (Set.empty_subset _)
  classical
  let I : Finset R := Finset.univ.filter (fun i => i ∈ b)
  have hrowI : Set.range (M.submatrix ((↑) : I → R) id).row = M.row '' b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.1, (Finset.mem_filter.1 i.2).2, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩, rfl⟩
  have hspan' : Submodule.span K (Set.range M.row) = Submodule.span K (M.row '' b) := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hspan ⟨i, Set.mem_univ _, rfl⟩
    · apply Submodule.span_mono; rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  have hr : (M.submatrix ((↑) : I → R) id).rank = M.rank := by
    rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, hrowI, hspan']
  have hli' : LinearIndependent K (M.submatrix ((↑) : I → R) id).row := by
    have : LinearIndependent K (fun i : b => M.row i) := hli
    let f : I → b := fun i => ⟨i.1, (Finset.mem_filter.1 i.2).2⟩
    have hf : Function.Injective f := fun x y h => Subtype.ext (by simpa [f] using congrArg Subtype.val h)
    exact this.comp f hf
  refine ⟨I, ?_, hr⟩
  rw [← hr, hli'.rank_matrix, Fintype.card_coe]

theorem exists_full_sub_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K] [DecidableEq R]
    [DecidableEq C] (M : Matrix R C K) :
    ∃ I : Finset R, ∃ J : Finset C, I.card = M.rank ∧ J.card = M.rank ∧
      MatrixSubRank M I J = M.rank := by
  obtain ⟨I, hI, hr⟩ := exists_rows_NS M
  obtain ⟨J, hJ, hr2⟩ := exists_rows_NS (M.submatrix ((↑) : I → R) id)ᵀ
  rw [Matrix.rank_transpose] at hJ hr2
  refine ⟨I, J, hI, by rw [hJ, hr], ?_⟩
  unfold MatrixSubRank
  rw [← hr, ← hr2, ← Matrix.rank_transpose]
  rfl

theorem rank_congr_NS {R C K : Type*} [Field K] (M : Matrix R C K)
    {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (f : α → R) (g : β → C) (f' : α' → R) (g' : β' → C) (ea : α' ≃ α) (eb : β' ≃ β)
    (hf : ∀ a, f (ea a) = f' a) (hg : ∀ b, g (eb b) = g' b) :
    (M.submatrix f' g').rank = (M.submatrix f g).rank := by
  have : M.submatrix f' g' = (M.submatrix f g).submatrix ea eb := by
    ext a b; simp [hf, hg]
  rw [this, Matrix.rank_submatrix]

def subEquivNS {R : Type*} (I0 : Finset R) (S : Finset R) (S' : Finset I0)
    (hS : ∀ x : I0, x ∈ S' ↔ (x : R) ∈ S) (hSI : S ⊆ I0) : {x // x ∈ S'} ≃ {y // y ∈ S} where
  toFun x := ⟨x.1.1, (hS _).1 x.2⟩
  invFun y := ⟨⟨y.1, hSI y.2⟩, (hS _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem subrank_sub_NS {R C K : Type*} [Fintype R] [Fintype C] [Field K]
    (M : Matrix R C K) (I0 : Finset R) (J0 : Finset C) (S : Finset R) (T : Finset C)
    (S' : Finset I0) (T' : Finset J0) (hS : ∀ x : I0, x ∈ S' ↔ (x : R) ∈ S)
    (hT : ∀ x : J0, x ∈ T' ↔ (x : C) ∈ T) (hSI : S ⊆ I0) (hTJ : T ⊆ J0) :
    MatrixSubRank (M.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) S' T' = MatrixSubRank M S T ∧
      S'.card = S.card ∧ T'.card = T.card := by
  refine ⟨?_, ?_, ?_⟩
  · unfold MatrixSubRank
    rw [Matrix.submatrix_submatrix]
    exact rank_congr_NS M _ _ _ _ (subEquivNS I0 S S' hS hSI) (subEquivNS J0 T T' hT hTJ)
      (fun a => rfl) (fun b => rfl)
  · rw [← Fintype.card_coe, ← Fintype.card_coe S]
    exact Fintype.card_congr (subEquivNS I0 S S' hS hSI)
  · rw [← Fintype.card_coe, ← Fintype.card_coe T]
    exact Fintype.card_congr (subEquivNS J0 T T' hT hTJ)


theorem rank_max_core {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    A.rank = (Finset.univ : Finset (Finset R)).sup (fun I =>
      (Finset.univ : Finset (Finset C)).sup (fun J =>
        MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)) := by
  have hAeq : A = Q.map (algebraMap K F) + T := by
    ext i j; rw [hA.1 i j]; rfl
  have hsubA : ∀ (I0 : Finset R) (J0 : Finset C),
      A.submatrix ((↑) : I0 → R) ((↑) : J0 → C) =
        (Q.submatrix ((↑) : I0 → R) ((↑) : J0 → C)).map (algebraMap K F) +
          T.submatrix ((↑) : I0 → R) ((↑) : J0 → C) := by
    intro I0 J0; rw [hAeq]; rfl
  have hind : ∀ (I0 : Finset R) (J0 : Finset C), AlgebraicIndependent K
      (fun x : {p : I0 × J0 // T.submatrix ((↑) : I0 → R) ((↑) : J0 → C) p.1 p.2 ≠ 0} =>
        T.submatrix ((↑) : I0 → R) ((↑) : J0 → C) x.1.1 x.1.2) := by
    intro I0 J0
    have := hA.2.comp
      (fun p : {p : I0 × J0 // T.submatrix ((↑) : I0 → R) ((↑) : J0 → C) p.1 p.2 ≠ 0} =>
        (⟨((p.1.1 : R), (p.1.2 : C)), p.2⟩ : {p : R × C // T p.1 p.2 ≠ 0}))
      (by
        intro x y h
        have h2 : ((x.1.1 : R), (x.1.2 : C)) = ((y.1.1 : R), (y.1.2 : C)) :=
          congrArg Subtype.val h
        rw [Prod.mk.injEq] at h2
        exact Subtype.ext (Prod.ext (Subtype.ext h2.1) (Subtype.ext h2.2)))
    exact this
  apply le_antisymm
  · obtain ⟨I0, J0, hI0, hJ0, hr⟩ := exists_full_sub_NS A
    have hc : Fintype.card I0 = Fintype.card J0 := by simp [hI0, hJ0]
    let e' := Fintype.equivOfCardEq hc
    have hd := (rank_full_iff_det_NS (A.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) e').1 (by
      unfold MatrixSubRank at hr; rw [hr, Fintype.card_coe, hI0])
    rw [hsubA] at hd
    obtain ⟨I', J', hQ', hT'⟩ := forward_NS _ _ e' hd
    let I : Finset R := I'.map (Function.Embedding.subtype _)
    let J : Finset C := J'.map (Function.Embedding.subtype _)
    have hIm : ∀ x : I0, x ∈ I' ↔ (x : R) ∈ I := by
      intro x; simp [I]
    have hJm : ∀ x : J0, x ∈ J' ↔ (x : C) ∈ J := by
      intro x; simp [J]
    have hII0 : I ⊆ I0 := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
      exact a.2
    have hJJ0 : J ⊆ J0 := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
      exact a.2
    obtain ⟨hq, -, -⟩ := subrank_sub_NS Q I0 J0 I J I' J' hIm hJm hII0 hJJ0
    have hTle : MatrixSubRank (T.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) I'ᶜ J'ᶜ ≤
        MatrixSubRank T Iᶜ Jᶜ := by
      unfold MatrixSubRank
      have : (T.submatrix ((↑) : I0 → R) ((↑) : J0 → C)).submatrix
          ((↑) : (I'ᶜ : Finset I0) → I0) ((↑) : (J'ᶜ : Finset J0) → J0) =
          (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C)).submatrix
            (fun x => ⟨x.1.1, Finset.mem_compl.2
              (fun h => (Finset.mem_compl.1 x.2) ((hIm x.1).2 h))⟩)
            (fun y => ⟨y.1.1, Finset.mem_compl.2
              (fun h => (Finset.mem_compl.1 y.2) ((hJm y.1).2 h))⟩) := rfl
      rw [this]
      exact Matrix.rank_submatrix_le _ _ _
    have hcard := Finset.card_le_univ I'
    have hcc : I'ᶜ.card = Fintype.card I0 - I'.card := Finset.card_compl I'
    rw [Fintype.card_coe] at hcard hcc
    calc A.rank = I'.card + I'ᶜ.card := by omega
      _ = MatrixSubRank Q I J + MatrixSubRank (T.submatrix ((↑) : I0 → R) ((↑) : J0 → C))
            I'ᶜ J'ᶜ := by rw [← hq, hQ'.2, hT'.2]
      _ ≤ MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ := add_le_add le_rfl hTle
      _ ≤ _ := Finset.le_sup_of_le (Finset.mem_univ I)
            (Finset.le_sup (f := fun J => MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)
              (Finset.mem_univ J))
  · refine Finset.sup_le (fun I _ => Finset.sup_le (fun J _ => ?_))
    -- pieces from Q
    obtain ⟨I1', J1', hc1, hc1', hr1⟩ :=
      exists_full_sub_NS (Q.submatrix ((↑) : I → R) ((↑) : J → C))
    let I1 : Finset R := I1'.map (Function.Embedding.subtype _)
    let J1 : Finset C := J1'.map (Function.Embedding.subtype _)
    have hI1m : ∀ x : I, x ∈ I1' ↔ (x : R) ∈ I1 := by intro x; simp [I1]
    have hJ1m : ∀ x : J, x ∈ J1' ↔ (x : C) ∈ J1 := by intro x; simp [J1]
    have hI1 : I1 ⊆ I := by
      intro x hx; obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx; exact a.2
    have hJ1 : J1 ⊆ J := by
      intro x hx; obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx; exact a.2
    obtain ⟨hq1, hq1c, hq1c'⟩ := subrank_sub_NS Q I J I1 J1 I1' J1' hI1m hJ1m hI1 hJ1
    -- pieces from T
    obtain ⟨I2', J2', hc2, hc2', hr2⟩ :=
      exists_full_sub_NS (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C))
    let I2 : Finset R := I2'.map (Function.Embedding.subtype _)
    let J2 : Finset C := J2'.map (Function.Embedding.subtype _)
    have hI2m : ∀ x : (Iᶜ : Finset R), x ∈ I2' ↔ (x : R) ∈ I2 := by intro x; simp [I2]
    have hJ2m : ∀ x : (Jᶜ : Finset C), x ∈ J2' ↔ (x : C) ∈ J2 := by intro x; simp [J2]
    have hI2 : I2 ⊆ Iᶜ := by
      intro x hx; obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx; exact a.2
    have hJ2 : J2 ⊆ Jᶜ := by
      intro x hx; obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx; exact a.2
    obtain ⟨hq2, hq2c, hq2c'⟩ := subrank_sub_NS T Iᶜ Jᶜ I2 J2 I2' J2' hI2m hJ2m hI2 hJ2
    -- numbers
    set r1 := MatrixSubRank Q I J with hr1def
    set r2 := MatrixSubRank T Iᶜ Jᶜ with hr2def
    have e1 : (Q.submatrix ((↑) : I → R) ((↑) : J → C)).rank = r1 := rfl
    have e2 : (T.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset C) → C)).rank = r2 :=
      rfl
    rw [e1] at hc1 hc1' hr1
    rw [e2] at hc2 hc2' hr2
    have hdI : Disjoint I1 I2 := Finset.disjoint_of_subset_left hI1
      (Finset.disjoint_of_subset_right hI2 (disjoint_compl_right))
    have hdJ : Disjoint J1 J2 := Finset.disjoint_of_subset_left hJ1
      (Finset.disjoint_of_subset_right hJ2 (disjoint_compl_right))
    let I0 := I1 ∪ I2
    let J0 := J1 ∪ J2
    have hI0c : I0.card = r1 + r2 := by
      rw [Finset.card_union_of_disjoint hdI, ← hq1c, ← hq2c, hc1, hc2]
    have hJ0c : J0.card = r1 + r2 := by
      rw [Finset.card_union_of_disjoint hdJ, ← hq1c', ← hq2c', hc1', hc2']
    let I' : Finset I0 := Finset.univ.filter (fun x => (x : R) ∈ I1)
    let J' : Finset J0 := Finset.univ.filter (fun x => (x : C) ∈ J1)
    have hI'm : ∀ x : I0, x ∈ I' ↔ (x : R) ∈ I1 := by intro x; simp [I']
    have hJ'm : ∀ x : J0, x ∈ J' ↔ (x : C) ∈ J1 := by intro x; simp [J']
    have hI'cm : ∀ x : I0, x ∈ I'ᶜ ↔ (x : R) ∈ I2 := by
      intro x
      rw [Finset.mem_compl, hI'm]
      have hx := x.2
      simp only [I0, Finset.mem_union] at hx
      constructor
      · intro h; tauto
      · intro h h1; exact Finset.disjoint_left.1 hdI h1 h
    have hJ'cm : ∀ x : J0, x ∈ J'ᶜ ↔ (x : C) ∈ J2 := by
      intro x
      rw [Finset.mem_compl, hJ'm]
      have hx := x.2
      simp only [J0, Finset.mem_union] at hx
      constructor
      · intro h; tauto
      · intro h h1; exact Finset.disjoint_left.1 hdJ h1 h
    obtain ⟨sq, sqc, sqc'⟩ := subrank_sub_NS Q I0 J0 I1 J1 I' J' hI'm hJ'm
      Finset.subset_union_left Finset.subset_union_left
    obtain ⟨st, stc, stc'⟩ := subrank_sub_NS T I0 J0 I2 J2 I'ᶜ J'ᶜ hI'cm hJ'cm
      Finset.subset_union_right Finset.subset_union_right
    have hQ' : IsNonsingularSub (Q.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) I' J' := by
      refine ⟨by rw [sqc, sqc', ← hq1c, ← hq1c', hc1, hc1'], ?_⟩
      rw [sq, sqc, ← hq1, hr1, ← hq1c, hc1]
    have hT' : IsNonsingularSub (T.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) I'ᶜ J'ᶜ := by
      refine ⟨by rw [stc, stc', ← hq2c, ← hq2c', hc2, hc2'], ?_⟩
      rw [st, stc, ← hq2, hr2, ← hq2c, hc2]
    have hc : Fintype.card I0 = Fintype.card J0 := by rw [Fintype.card_coe, Fintype.card_coe, hI0c, hJ0c]
    let e' := Fintype.equivOfCardEq hc
    have hd := backward_NS _ _ e' (hind I0 J0) I' J' hQ' hT'
    rw [← hsubA] at hd
    have hrk := (rank_full_iff_det_NS (A.submatrix ((↑) : I0 → R) ((↑) : J0 → C)) e').2 hd
    rw [Fintype.card_coe, hI0c] at hrk
    rw [← hrk]
    exact Matrix.rank_submatrix_le _ _ _

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices


theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    A.rank = (Finset.univ : Finset (Finset R)).sup (fun I =>
      (Finset.univ : Finset (Finset C)).sup (fun J =>
        MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)) := by
  exact rank_max_core A Q T hA
