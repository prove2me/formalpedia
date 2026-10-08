-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.mixed_poly_matrix_deg_det_max_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:21:58.874294+00:00
-- url     : https://prove2.me/submissions/59bc9c58-cb0a-46f9-8502-124602d9db73

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedPolyMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_SubDegDet



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



/-- block determinant with a zero block, up to sign. -/
theorem block_det_NS {R α : Type*} [Fintype R] [DecidableEq R] [CommRing α]
    (M : Matrix R R α) (I J : Finset R) (e1 : I ≃ J) (e2 : (Iᶜ : Finset R) ≃ (Jᶜ : Finset R))
    (hz : ∀ i ∈ I, ∀ j ∉ J, M i j = 0) :
    ∃ u : ℤˣ, M.det = (u : α) * ((Matrix.det (Matrix.of fun a b : I => M a (e1 b))) *
      (Matrix.det (Matrix.of fun a b : (Iᶜ : Finset R) => M a (e2 b)))) := by
  let cI : (Iᶜ : Finset R) ≃ {x // ¬ x ∈ I} := Equiv.subtypeEquivRight (fun x => Finset.mem_compl)
  let cJ : (Jᶜ : Finset R) ≃ {x // ¬ x ∈ J} := Equiv.subtypeEquivRight (fun x => Finset.mem_compl)
  let σ : I ⊕ (Iᶜ : Finset R) ≃ R :=
    (Equiv.sumCongr (Equiv.refl _) cI).trans (Equiv.sumCompl (fun x => x ∈ I))
  let τ : I ⊕ (Iᶜ : Finset R) ≃ R :=
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCongr (Equiv.refl _) cJ)).trans
      (Equiv.sumCompl (fun x => x ∈ J))
  have hblk : M.submatrix σ τ = Matrix.fromBlocks (Matrix.of fun a b : I => M a (e1 b)) 0
      (Matrix.of fun (a : (Iᶜ : Finset R)) (b : I) => M a (e1 b))
      (Matrix.of fun a b : (Iᶜ : Finset R) => M a (e2 b)) := by
    ext x y
    rcases x with a | a <;> rcases y with b | b
    · rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      apply hz _ a.2
      have := (e2 b).2
      exact Finset.mem_compl.1 this
    · rfl
    · rfl
  have h1 : (M.submatrix σ τ).det = (M.submatrix id (σ.symm.trans τ)).det := by
    have : M.submatrix σ τ = (M.submatrix id (σ.symm.trans τ)).submatrix σ σ := by
      ext x y; simp
    rw [this, Matrix.det_submatrix_equiv_self]
  have key : ((Equiv.Perm.sign (σ.symm.trans τ) : ℤ) : α) * M.det =
      (Matrix.det (Matrix.of fun a b : I => M a (e1 b))) *
      (Matrix.det (Matrix.of fun a b : (Iᶜ : Finset R) => M a (e2 b))) := by
    rw [← Matrix.det_permute', ← h1, hblk, Matrix.det_fromBlocks_zero₁₂]
  refine ⟨Equiv.Perm.sign (σ.symm.trans τ), ?_⟩
  have h2 : ((Equiv.Perm.sign (σ.symm.trans τ) : ℤ) : α) *
      ((Equiv.Perm.sign (σ.symm.trans τ) : ℤ) : α) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [← key, ← mul_assoc, h2, one_mul]


theorem blockcard_NS {R L : Type*} [Fintype R] [DecidableEq R] [Field L]
    (N : Matrix R R L) (I J : Finset R) (hN : ∀ i j, N i j ≠ 0 → (i ∈ I ↔ j ∈ J))
    (hd : N.det ≠ 0) : I.card = J.card := by
  have hrank : N.rank = Fintype.card R := Matrix.rank_of_det_ne_zero hd
  set N1 : Matrix R R L := Matrix.of fun i j => if i ∈ I then N i j else 0 with hN1
  set N2 : Matrix R R L := Matrix.of fun i j => if i ∈ I then 0 else N i j with hN2
  have hN12 : N = N1 + N2 := by
    ext i j; simp only [hN1, hN2, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  have h1 : N1.rank ≤ (N1.submatrix ((↑) : I → R) ((↑) : J → R)).rank :=
    rank_le_sub_NS N1 I J (fun i j hij => by
      simp only [hN1, Matrix.of_apply] at hij
      split_ifs at hij with hi
      · exact ⟨hi, (hN i j hij).1 hi⟩
      · exact absurd rfl hij)
  have h2 : N2.rank ≤ (N2.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset R) → R)).rank :=
    rank_le_sub_NS N2 Iᶜ Jᶜ (fun i j hij => by
      simp only [hN2, Matrix.of_apply] at hij
      split_ifs at hij with hi
      · exact absurd rfl hij
      · refine ⟨Finset.mem_compl.2 hi, Finset.mem_compl.2 (fun hj => hi ((hN i j hij).2 hj))⟩)
  have hsum := rank_add_le_NS N1 N2
  rw [← hN12, hrank] at hsum
  have a1 := Matrix.rank_le_card_height (N1.submatrix ((↑) : I → R) ((↑) : J → R))
  have a2 := Matrix.rank_le_card_width (N1.submatrix ((↑) : I → R) ((↑) : J → R))
  have b1 := Matrix.rank_le_card_height
    (N2.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset R) → R))
  have b2 := Matrix.rank_le_card_width
    (N2.submatrix ((↑) : (Iᶜ : Finset R) → R) ((↑) : (Jᶜ : Finset R) → R))
  simp only [Fintype.card_coe, Finset.card_compl] at a1 a2 b1 b2
  have hIR : I.card ≤ Fintype.card R := Finset.card_le_univ I
  have hJC : J.card ≤ Fintype.card R := Finset.card_le_univ J
  omega

theorem blockcard_poly_NS {R F : Type*} [Fintype R] [DecidableEq R] [Field F]
    (N : Matrix R R (Polynomial F)) (I J : Finset R) (hN : ∀ i j, N i j ≠ 0 → (i ∈ I ↔ j ∈ J))
    (hd : N.det ≠ 0) : I.card = J.card := by
  let L := FractionRing (Polynomial F)
  let f := algebraMap (Polynomial F) L
  have hf : Function.Injective f := IsFractionRing.injective _ _
  apply blockcard_NS (N.map f) I J
  · intro i j h
    apply hN
    intro h0; apply h; simp [h0]
  · intro h0
    apply hd
    apply hf
    rw [RingHom.map_det, map_zero]
    exact h0

theorem degree_unit_mul_NS {F : Type*} [Field F] (u : ℤˣ) (p : Polynomial F) :
    (((u : ℤ) : Polynomial F) * p).degree = p.degree := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]


theorem degdet_le_NS {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F)) :
    (Matrix.det (Q.map (Polynomial.map (algebraMap K F)) + T)).degree ≤
      ((Finset.univ : Finset (Finset R × Finset R)).filter
          (fun p => p.1.card = p.2.card)).sup
        (fun p => SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) := by
  set Qm := Q.map (Polynomial.map (algebraMap K F)) with hQm
  rw [det_add_colmixNS]
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le (fun J _ => ?_))
  have hsplit : colmixNS J Qm T = colmixNS J Qm 0 + colmixNS J 0 T := by
    ext i j; simp only [colmixNS, Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
    split_ifs <;> simp
  rw [hsplit, det_add_rowmixNS]
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le (fun I _ => ?_))
  set N := rowmixNS I (colmixNS J Qm 0) (colmixNS J 0 T) with hN
  by_cases hN0 : N.det = 0
  · rw [hN0, Polynomial.degree_zero]; exact bot_le
  have hpat : ∀ i j, N i j ≠ 0 → (i ∈ I ↔ j ∈ J) := by
    intro i j h
    simp only [hN, rowmixNS, colmixNS, Matrix.of_apply, Matrix.zero_apply] at h
    split_ifs at h <;> simp_all
  have hIJ := blockcard_poly_NS N I J hpat hN0
  have h1 : Fintype.card I = Fintype.card J := by simp [hIJ]
  have h2 : Fintype.card (Iᶜ : Finset R) = Fintype.card (Jᶜ : Finset R) := by
    simp [Finset.card_compl, hIJ]
  obtain ⟨u, hu⟩ := block_det_NS N I J (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2)
    (by intro i hi j hj; simp [hN, rowmixNS, colmixNS, hi, hj])
  have hA1 : (Matrix.of fun a b : I => N a (Fintype.equivOfCardEq h1 b)) =
      (Matrix.of fun a b : I => Q a (Fintype.equivOfCardEq h1 b)).map
        (Polynomial.mapRingHom (algebraMap K F)) := by
    ext a b
    simp [hN, rowmixNS, colmixNS, a.2, (Fintype.equivOfCardEq h1 b).2, hQm]
  have hD1 : (Matrix.of fun a b : (Iᶜ : Finset R) => N a (Fintype.equivOfCardEq h2 b)) =
      (Matrix.of fun a b : (Iᶜ : Finset R) => T a (Fintype.equivOfCardEq h2 b)) := by
    ext a b
    have ha := Finset.mem_compl.1 a.2
    have hb := Finset.mem_compl.1 (Fintype.equivOfCardEq h2 b).2
    simp [hN, rowmixNS, colmixNS, ha, hb]
  have hdm : ((Matrix.of fun a b : I => Q a (Fintype.equivOfCardEq h1 b)).map
        (Polynomial.mapRingHom (algebraMap K F))).det =
      Polynomial.mapRingHom (algebraMap K F)
        (Matrix.of fun a b : I => Q a (Fintype.equivOfCardEq h1 b)).det :=
    (RingHom.map_det _ _).symm
  rw [hu, hA1, hD1, hdm, degree_unit_mul_NS, Polynomial.degree_mul,
    Polynomial.coe_mapRingHom, Polynomial.degree_map]
  have hmem : (I, J) ∈ (Finset.univ : Finset (Finset R × Finset R)).filter
      (fun p => p.1.card = p.2.card) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hIJ⟩
  have hle := Finset.le_sup (f := fun p : Finset R × Finset R =>
      SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) hmem
  refine le_trans (le_of_eq ?_) hle
  simp only [SubDegDet, dif_pos h1, dif_pos h2]
  rfl


open Polynomial in
theorem spec_coeff_NS {R K : Type*} [Fintype R] [Field K] [DecidableEq R]
    (Q : Matrix R R K[X]) (I J : Finset R) (e1 : I ≃ J)
    (π : (Iᶜ : Finset R) ≃ (Jᶜ : Finset R)) (κ : (Iᶜ : Finset R) → ℕ)
    (hq : (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))) ≠ 0)
    (P0 : Matrix R R K[X])
    (hP : ∀ i j, P0 i j = if h : i ∉ I then
      (if j = (π ⟨i, Finset.mem_compl.2 h⟩ : R) then X ^ (κ ⟨i, Finset.mem_compl.2 h⟩) else 0)
      else 0) :
    (Matrix.det (Q.map (Polynomial.map Polynomial.C) +
      Matrix.of fun i j => Polynomial.C (X : K[X]) * (P0 i j).map Polynomial.C)).coeff
      ((Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).natDegree + ∑ k, κ k) ≠ 0 := by
  set qd := Matrix.det (Matrix.of fun a b : I => Q a (e1 b)) with hqd
  set n := qd.natDegree + ∑ k, κ k with hn
  rw [det_add_colmixNS]
  have hterm : ∀ S : Finset R, (colmixNS S (Q.map (Polynomial.map Polynomial.C))
      (Matrix.of fun i j => Polynomial.C (X : K[X]) * (P0 i j).map Polynomial.C)).det =
      Polynomial.C ((X : K[X]) ^ (Finset.univ.filter (fun k => k ∉ S)).card) *
        ((colmixNS S Q P0).det).map Polynomial.C := by
    intro S
    have hM : colmixNS S (Q.map (Polynomial.map Polynomial.C))
        (Matrix.of fun i j => Polynomial.C (X : K[X]) * (P0 i j).map Polynomial.C) =
        Matrix.of fun i k => (fun k => if k ∈ S then (1 : K[X][X]) else Polynomial.C X) k *
          ((colmixNS S Q P0).map (Polynomial.mapRingHom Polynomial.C)) i k := by
      ext i k : 1
      simp only [colmixNS, Matrix.of_apply, Matrix.map_apply]
      split_ifs <;> simp
    rw [hM, Matrix.det_mul_row, show ((colmixNS S Q P0).map
        (Polynomial.mapRingHom Polynomial.C)).det =
        Polynomial.mapRingHom Polynomial.C (colmixNS S Q P0).det from (RingHom.map_det _ _).symm]
    congr 1
    rw [Finset.prod_ite]
    simp
  simp_rw [hterm]
  intro h0
  have hc := congrArg (fun p => Polynomial.coeff p (Finset.univ.filter (fun k => k ∉ J)).card) h0
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single J] at hc
  · rw [mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
    -- compute D_J
    obtain ⟨u, hu⟩ := block_det_NS (colmixNS J Q P0) I J e1 π (by
      intro i hi j hj
      simp only [colmixNS, Matrix.of_apply, if_neg hj, hP]
      rw [dif_neg (not_not.2 hi)])
    have hA : (Matrix.of fun a b : I => colmixNS J Q P0 a (e1 b)) =
        Matrix.of fun a b : I => Q a (e1 b) := by
      ext a b; simp [colmixNS, (e1 b).2]
    have hD : (Matrix.of fun a b : (Iᶜ : Finset R) => colmixNS J Q P0 a (π b)) =
        Matrix.diagonal (fun a => (X : K[X]) ^ (κ a)) := by
      ext a b
      have hb := Finset.mem_compl.1 (π b).2
      have ha := Finset.mem_compl.1 a.2
      simp only [colmixNS, Matrix.of_apply, if_neg hb, hP, dif_pos ha, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg]
        intro h
        apply hab
        have : π b = π a := Subtype.ext h
        exact (π.injective this).symm
    rw [hu, hA, hD, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← hqd] at hc
    rcases Int.units_eq_one_or u with h | h
    · rw [h] at hc
      simp only [Units.val_one, Int.cast_one, one_mul] at hc
      rw [hn, Polynomial.coeff_mul_X_pow] at hc
      exact hq (Polynomial.leadingCoeff_eq_zero.1 hc)
    · rw [h] at hc
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
        Polynomial.coeff_neg, neg_eq_zero] at hc
      rw [hn, Polynomial.coeff_mul_X_pow] at hc
      exact hq (Polynomial.leadingCoeff_eq_zero.1 hc)
  · intro S _ hSJ
    rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hcard
    · by_contra hd
      have hJS : J ⊆ S := by
        intro j hj
        by_contra hjS
        apply hd
        rw [Matrix.det_eq_zero_of_column_eq_zero j, Polynomial.coeff_zero]
        intro i
        simp only [colmixNS, Matrix.of_apply, if_neg hjS, hP]
        by_cases h1 : i ∉ I
        · rw [dif_pos h1, if_neg]
          intro h2
          have h3 := (π ⟨i, Finset.mem_compl.2 h1⟩).2
          rw [← h2, Finset.mem_compl] at h3
          exact h3 hj
        · rw [dif_neg h1]
      apply hSJ
      have hsub : Finset.univ.filter (fun k => k ∉ S) ⊆ Finset.univ.filter (fun k => k ∉ J) := by
        intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h hk => h (hJS hk)
      have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      ext j
      have := congrArg (fun s => j ∈ s) heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      tauto
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h


theorem matching_NS {α β F : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Field F]
    (T : α → β → Polynomial F) (e2 : α ≃ β)
    (htd : Matrix.det (Matrix.of fun a b => T a (e2 b)) ≠ 0) :
    ∃ π : α ≃ β, ∃ κ : α → ℕ, (∀ i, (T i (π i)).coeff (κ i) ≠ 0) ∧
      (Matrix.det (Matrix.of fun a b => T a (e2 b))).natDegree ≤ ∑ i, κ i := by
  classical
  set M : Matrix α α (Polynomial F) := Matrix.of fun a b => T a (e2 b) with hM
  let S := Finset.univ.filter (fun σ : Equiv.Perm α => ∏ i, M (σ i) i ≠ 0)
  have hS : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply htd
    rw [Matrix.det_apply']
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    have : σ ∉ S := by rw [hne]; exact Finset.notMem_empty _
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
    rw [this, mul_zero]
  obtain ⟨σ0, hσ0S, hmax⟩ := S.exists_max_image (fun σ => (∏ i, M (σ i) i).natDegree) hS
  have hσ0 : ∏ i, M (σ0 i) i ≠ 0 := (Finset.mem_filter.1 hσ0S).2
  have hall : ∀ i, M (σ0 i) i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hσ0) i (Finset.mem_univ _)
  have hdeg : M.det.natDegree ≤ (∏ i, M (σ0 i) i).natDegree := by
    rw [Matrix.det_apply']
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    by_cases hσ : σ ∈ S
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h1 : (((Equiv.Perm.sign σ : ℤ) : Polynomial F)).natDegree = 0 :=
        Polynomial.natDegree_intCast _
      rw [h1, zero_add]
      exact hmax σ hσ
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hσ
      rw [hσ, mul_zero, Polynomial.natDegree_zero]; exact Nat.zero_le _
  rw [Polynomial.natDegree_prod _ _ (fun i _ => hall i)] at hdeg
  refine ⟨σ0.symm.trans e2, fun a => (T a ((σ0.symm.trans e2) a)).natDegree, ?_, ?_⟩
  · intro a
    rw [Polynomial.coeff_natDegree, Ne, Polynomial.leadingCoeff_eq_zero]
    have := hall (σ0.symm a)
    simpa [hM] using this
  · refine hdeg.trans (le_of_eq ?_)
    rw [← Equiv.sum_comp σ0 (fun a => (T a ((σ0.symm.trans e2) a)).natDegree)]
    simp [hM]


open Polynomial in
theorem coeff_ne_zero_NS {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (Q : Matrix R R K[X]) (T : Matrix R R F[X])
    (hT : AlgebraicIndependent K
      (fun e : {p : R × R × ℕ // (T p.1 p.2.1).coeff p.2.2 ≠ 0} =>
        (T e.1.1 e.1.2.1).coeff e.1.2.2))
    (I J : Finset R) (e1 : I ≃ J) (π : (Iᶜ : Finset R) ≃ (Jᶜ : Finset R))
    (κ : (Iᶜ : Finset R) → ℕ) (hκ : ∀ i : (Iᶜ : Finset R), (T i (π i)).coeff (κ i) ≠ 0)
    (hq : (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))) ≠ 0) :
    (Matrix.det (Q.map (Polynomial.map (algebraMap K F)) + T)).coeff
      ((Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).natDegree + ∑ k, κ k) ≠ 0 := by
  classical
  set n := (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).natDegree + ∑ k, κ k with hn
  let E := {p : R × R × ℕ // (T p.1 p.2.1).coeff p.2.2 ≠ 0}
  let D := MvPolynomial E K
  let x : E → F := fun e => (T e.1.1 e.1.2.1).coeff e.1.2.2
  let G : Matrix R R D[X] := Matrix.of fun i j =>
    (Q i j).map (algebraMap K D) + ∑ m ∈ (T i j).support.attach,
      Polynomial.C (MvPolynomial.X (⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ : E)) *
        Polynomial.X ^ m.1
  let y : E → K[X] := fun e =>
    if hi : e.1.1 ∉ I then
      (if e.1.2.1 = (π ⟨e.1.1, Finset.mem_compl.2 hi⟩ : R) ∧
          e.1.2.2 = κ ⟨e.1.1, Finset.mem_compl.2 hi⟩ then Polynomial.X else 0)
    else 0
  let P0 : Matrix R R K[X] := Matrix.of fun i j => if h : i ∉ I then
      (if j = (π ⟨i, Finset.mem_compl.2 h⟩ : R) then X ^ (κ ⟨i, Finset.mem_compl.2 h⟩) else 0)
      else 0
  have hGA : G.map (Polynomial.map (MvPolynomial.aeval x).toRingHom) =
      Q.map (Polynomial.map (algebraMap K F)) + T := by
    ext i j : 1
    simp only [G, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Polynomial.map_add,
      Polynomial.map_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    congr 1
    · congr 1
      ext c; simp
    · refine (Finset.sum_congr rfl (fun m _ => ?_)).trans
        ((Finset.sum_attach (T i j).support (fun m => Polynomial.C
          ((T i j).coeff m) * Polynomial.X ^ m)).trans
          (Polynomial.as_sum_support_C_mul_X_pow (T i j)).symm)
      simp only [x]
      congr 2
      exact MvPolynomial.aeval_X _ _
  have hGS : G.map (Polynomial.map (MvPolynomial.aeval y).toRingHom) =
      Q.map (Polynomial.map Polynomial.C) +
        Matrix.of fun i j => Polynomial.C (X : K[X]) * (P0 i j).map Polynomial.C := by
    ext i j : 1
    simp only [G, P0, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Polynomial.map_add,
      Polynomial.map_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    congr 1
    · congr 1
      ext c; simp
    · have hyX : ∀ m : (T i j).support, (MvPolynomial.aeval (R := K) y).toRingHom
          (MvPolynomial.X (⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ : E)) =
          y ⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ := fun m => MvPolynomial.aeval_X y _
      simp only [hyX]
      by_cases hi : i ∉ I
      · rw [dif_pos hi]
        by_cases hj : j = (π ⟨i, Finset.mem_compl.2 hi⟩ : R)
        · rw [if_pos hj]
          have hmem : κ ⟨i, Finset.mem_compl.2 hi⟩ ∈ (T i j).support := by
            rw [Polynomial.mem_support_iff, hj]; exact hκ ⟨i, Finset.mem_compl.2 hi⟩
          rw [Finset.sum_eq_single ⟨κ ⟨i, Finset.mem_compl.2 hi⟩, hmem⟩]
          · simp only [y, dif_pos hi, hj, and_self, if_true]
            simp
          · intro m _ hm
            have : y ⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ = 0 := by
              simp only [y, dif_pos hi]
              rw [if_neg]
              rintro ⟨-, h2⟩
              exact hm (Subtype.ext h2)
            rw [this, Polynomial.C_0, zero_mul]
          · intro h; exact absurd (Finset.mem_attach _ _) h
        · rw [if_neg hj, Polynomial.map_zero, mul_zero]
          refine Finset.sum_eq_zero (fun m _ => ?_)
          have : y ⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ = 0 := by
            simp only [y, dif_pos hi]
            rw [if_neg]
            rintro ⟨h1, -⟩
            exact hj h1
          rw [this, Polynomial.C_0, zero_mul]
      · rw [dif_neg hi, Polynomial.map_zero, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        have : y ⟨(i, j, m.1), Polynomial.mem_support_iff.1 m.2⟩ = 0 := by
          simp only [y, dif_neg hi]
        rw [this, Polynomial.C_0, zero_mul]
  have hdetA : Matrix.det (Q.map (Polynomial.map (algebraMap K F)) + T) =
      (Matrix.det G).map (MvPolynomial.aeval x).toRingHom := by
    rw [← hGA]
    exact (RingHom.map_det (Polynomial.mapRingHom (MvPolynomial.aeval x).toRingHom) G).symm
  have hdetS : Matrix.det (Q.map (Polynomial.map Polynomial.C) +
        Matrix.of fun i j => Polynomial.C (X : K[X]) * (P0 i j).map Polynomial.C) =
      (Matrix.det G).map (MvPolynomial.aeval y).toRingHom := by
    rw [← hGS]
    exact (RingHom.map_det (Polynomial.mapRingHom (MvPolynomial.aeval y).toRingHom) G).symm
  have hspec := spec_coeff_NS Q I J e1 π κ hq P0 (fun i j => rfl)
  intro h0
  apply hspec
  rw [hdetS, Polynomial.coeff_map]
  rw [hdetA, Polynomial.coeff_map] at h0
  have : (Matrix.det G).coeff n = 0 := hT.eq_zero_of_aeval_eq_zero _ h0
  rw [← hn, this, map_zero]


theorem degdet_core {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (A : Matrix R R (Polynomial F)) (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F))
    (hA : IsMixedPolyMatrix A Q T) :
    (Matrix.det A).degree =
      ((Finset.univ : Finset (Finset R × Finset R)).filter
          (fun p => p.1.card = p.2.card)).sup
        (fun p => SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) := by
  have hAeq : A = Q.map (Polynomial.map (algebraMap K F)) + T := by
    ext i j; rw [hA.1 i j]; rfl
  rw [hAeq]
  apply le_antisymm (degdet_le_NS Q T)
  apply Finset.sup_le
  rintro ⟨I, J⟩ hp
  have hIJ : I.card = J.card := (Finset.mem_filter.1 hp).2
  have h1 : Fintype.card I = Fintype.card J := by simp [hIJ]
  have h2 : Fintype.card (Iᶜ : Finset R) = Fintype.card (Jᶜ : Finset R) := by simp [hIJ]
  simp only [SubDegDet, dif_pos h1, dif_pos h2]
  set e1 := Fintype.equivOfCardEq h1
  set e2 := Fintype.equivOfCardEq h2
  change (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).degree +
    (Matrix.det (Matrix.of fun a b : (Iᶜ : Finset R) => T a (e2 b))).degree ≤ _
  by_cases hq : Matrix.det (Matrix.of fun a b : I => Q a (e1 b)) = 0
  · rw [hq, Polynomial.degree_zero, WithBot.bot_add]; exact bot_le
  by_cases ht : Matrix.det (Matrix.of fun a b : (Iᶜ : Finset R) => T a (e2 b)) = 0
  · rw [ht, Polynomial.degree_zero, WithBot.add_bot]; exact bot_le
  obtain ⟨π, κ, hκ, hb⟩ := matching_NS
    (fun (a : (Iᶜ : Finset R)) (b : (Jᶜ : Finset R)) => T a b) e2 ht
  have hc := coeff_ne_zero_NS Q T hA.2 I J e1 π κ hκ hq
  have hle := Polynomial.le_degree_of_ne_zero hc
  rw [Polynomial.degree_eq_natDegree hq, Polynomial.degree_eq_natDegree ht]
  refine le_trans ?_ hle
  have : (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).natDegree +
      (Matrix.det (Matrix.of fun a b : (Iᶜ : Finset R) => T a (e2 b))).natDegree ≤
      (Matrix.det (Matrix.of fun a b : I => Q a (e1 b))).natDegree + ∑ k, κ k :=
    Nat.add_le_add_left hb _
  exact_mod_cast this

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices


theorem solution {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (A : Matrix R R (Polynomial F)) (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F))
    (hA : IsMixedPolyMatrix A Q T) :
    (Matrix.det A).degree =
      ((Finset.univ : Finset (Finset R × Finset R)).filter
          (fun p => p.1.card = p.2.card)).sup
        (fun p => SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) := by
  exact degdet_core A Q T hA
