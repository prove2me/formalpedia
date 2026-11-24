-- Prove2me | solution 1 for CommutativeRankNC.Approximation.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:27:15.853995+00:00
-- url     : https://prove2.me/submissions/c77c425d-bd25-4461-99b2-a3ede45516e9

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace Sol535Aux

open Matrix

lemma aux_exists_cols {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : Matrix m n K) (s : ℕ) (hs : s = B.rank) :
    ∃ g : Fin s → n, LinearIndependent K (fun j => B.col (g j)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range B.col)
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  let _ : Fintype b := hfin.fintype
  have hcard : Fintype.card b = s := by
    rw [hs, rank_eq_finrank_span_cols, ← hspan,
      finrank_span_set_eq_card (hli : LinearIndepOn K id b), Set.toFinset_card]
  let e : Fin s ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hch : ∀ x : b, ∃ j, B.col j = x := fun x => hbs x.2
  refine ⟨fun j => (hch (e j)).choose, ?_⟩
  have : (fun j => B.col ((hch (e j)).choose)) = ((↑) : b → (m → K)) ∘ e := by
    funext j; exact (hch (e j)).choose_spec
  rw [this]
  exact hli.comp e e.injective

lemma aux_exists_minor {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) :
    ∃ f : Fin A.rank → m, ∃ g : Fin A.rank → n, (A.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := aux_exists_cols A A.rank rfl
  set B : Matrix m (Fin A.rank) K := A.submatrix id g with hB
  have hBt : LinearIndependent K Bᵀ.row := by
    convert hg using 1
    funext j; funext i; rfl
  have hrk : Bᵀ.rank = A.rank := by
    rw [hBt.rank_matrix, Fintype.card_fin]
  obtain ⟨f, hf⟩ := aux_exists_cols Bᵀ A.rank hrk.symm
  refine ⟨f, g, ?_⟩
  have hD : LinearIndependent K (A.submatrix f g).row := by
    convert hf using 1
    funext j; funext i; rfl
  have hu := linearIndependent_rows_iff_isUnit.mp hD
  exact ((isUnit_iff_isUnit_det _).mp hu).ne_zero

lemma aux_le_rank_of_minor {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    {s : ℕ} (A : Matrix m n K) (f : Fin s → m) (g : Fin s → n)
    (h : (A.submatrix f g).det ≠ 0) : s ≤ A.rank := by
  have h1 : (A.submatrix f g).rank = s := by
    rw [rank_of_det_ne_zero h, Fintype.card_fin]
  rw [← h1, ← eRank_toNat_eq_rank, ← eRank_toNat_eq_rank]
  apply ENat.toNat_le_toNat (eRank_submatrix_le A f g)
  exact ne_top_of_le_ne_top (by simp) (eRank_le_card_width A)

end Sol535Aux

open Matrix CommutativeRankNC.Approximation Sol535Aux

theorem solution {n : ℕ} (A C : QMatrix n) :
    ∃ l : ℕ, l ≤ n ∧ (A + (l : ℚ) • C).rank = (affinePencil A C).rank := by
  classical
  set K := FractionRing (Polynomial ℚ)
  let P : Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
    Matrix.of fun i j => Polynomial.C (A i j) + Polynomial.X * Polynomial.C (C i j)
  have hPK : P.map (algebraMap (Polynomial ℚ) K) = affinePencil A C := by
    ext i j; simp [P, affinePencil]; rfl
  have hPe : ∀ q : ℚ, P.map (Polynomial.evalRingHom q) = A + q • C := by
    intro q; ext i j; simp [P]; ring
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) K) :=
    IsFractionRing.injective _ _
  -- determinant of a minor of the specialization is the evaluation of the polynomial minor
  have hdetE : ∀ (q : ℚ) {s : ℕ} (f g : Fin s → Fin n),
      ((A + q • C).submatrix f g).det = (P.submatrix f g).det.eval q := by
    intro q s f g
    rw [← hPe q, Matrix.submatrix_map, ← RingHom.mapMatrix_apply]
    exact (RingHom.map_det _ _).symm
  have hdetK : ∀ {s : ℕ} (f g : Fin s → Fin n),
      ((affinePencil A C).submatrix f g).det = algebraMap _ K (P.submatrix f g).det := by
    intro s f g
    rw [← hPK, Matrix.submatrix_map, ← RingHom.mapMatrix_apply]
    exact (RingHom.map_det _ _).symm
  set r := (affinePencil A C).rank
  have hrn : r ≤ n := by
    have := rank_le_card_width (affinePencil A C); simpa using this
  obtain ⟨f, g, hfg⟩ := aux_exists_minor (affinePencil A C)
  rw [hdetK] at hfg
  have hq : (P.submatrix f g).det ≠ 0 := fun h0 => hfg (by rw [h0, map_zero])
  have hdeg : (P.submatrix f g).det.natDegree ≤ r := by
    have : P.submatrix f g = (Polynomial.X : Polynomial ℚ) • (C.submatrix f g).map Polynomial.C
        + (A.submatrix f g).map Polynomial.C := by
      ext i j; simp [P]; ring
    rw [this]
    simpa using Polynomial.natDegree_det_X_add_C_le (C.submatrix f g) (A.submatrix f g)
  have hex : ∃ i : Fin (n+1), (P.submatrix f g).det.eval ((i : ℕ) : ℚ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hq
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun i : Fin (n+1) => ((i : ℕ) : ℚ))
    · intro a b hab
      have : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) := hab
      exact Fin.ext (by exact_mod_cast this)
    · exact hcon
    · simp; omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, by omega, le_antisymm ?_ ?_⟩
  · obtain ⟨f', g', h'⟩ := aux_exists_minor (A + ((i : ℕ) : ℚ) • C)
    apply aux_le_rank_of_minor _ f' g'
    rw [hdetK]
    intro h0
    apply h'
    rw [hdetE]
    have : (P.submatrix f' g').det = 0 := hinj (by rw [h0, map_zero])
    rw [this, Polynomial.eval_zero]
  · apply aux_le_rank_of_minor _ f g
    rw [hdetE]; exact hi

