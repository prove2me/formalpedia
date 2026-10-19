-- Prove2me | solution 1 for CauchyRiemannIndex.symplecticLoop_fixing_vector_homotopic_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:36:49.32827+00:00
-- url     : https://prove2.me/submissions/0a0133fd-7272-47b8-8084-9d3cf69ecf22

import Theorems.Thm_CauchyRiemannIndex_diagonal_isSymplectic
import Theorems.Thm_CauchyRiemannIndex_isSymplectic_left_of_diamond

open Matrix

namespace CRLK5

open CauchyRiemannIndex

/-- The fixed vector index `e = q_{n+1}`. -/
abbrev ie (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) := Sum.inl (Fin.last n)

/-- Its symplectic partner `f = p_{n+1}`. -/
abbrev jf (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) := Sum.inr (Fin.last n)

/-- The rescaled matrix: for `l ≠ 0` this is the conjugate `D A D⁻¹`,
`D = diag(l on e, l⁻¹ on f, 1 elsewhere)`. -/
def scaleM {n : ℕ} (l : ℝ) (A : Mat (n + 1)) : Mat (n + 1) :=
  Matrix.of fun i j =>
    if i = jf n ∨ j = ie n then A i j
    else (if i = ie n then l else 1) * (if j = jf n then l else 1) * A i j

lemma scaleM_apply {n : ℕ} (l : ℝ) (A : Mat (n + 1)) (i j) :
    scaleM l A i j = if i = jf n ∨ j = ie n then A i j
      else (if i = ie n then l else 1) * (if j = jf n then l else 1) * A i j := rfl

/-- Column `e` and row `f` of a symplectic matrix fixing `e` are unit vectors. -/
lemma col_e {n : ℕ} {A : Mat (n + 1)}
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) (i) :
    A i (ie n) = if i = ie n then 1 else 0 := by
  have := congrFun he i
  simp [Matrix.mulVec_single, Pi.single_apply] at this
  rw [this]

lemma row_f {n : ℕ} {A : Mat (n + 1)} (hA : IsSymplectic A)
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) (j) :
    A (jf n) j = if j = jf n then 1 else 0 := by
  have h := (SymplecticGroup.mem_iff'.mp hA)
  have h2 := congrFun (congrFun h (ie n)) j
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, col_e he] at h2
  simp [Matrix.J, Matrix.one_apply, Fintype.sum_sum_type, ite_and] at h2
  rcases j with j | j
  · simpa [Matrix.fromBlocks] using h2
  · by_cases hj : j = Fin.last n
    · subst hj; simpa [Matrix.fromBlocks] using h2
    · have hj' : Fin.last n ≠ j := fun h => hj h.symm
      simpa [Matrix.fromBlocks, Matrix.one_apply, hj, hj'] using h2

lemma ie_ne_jf (n : ℕ) : ie n ≠ jf n := by simp

/-- For `l ≠ 0`, `scaleM l A` is a conjugate of `A` by diagonal symplectic matrices. -/
lemma scaleM_eq_conj {n : ℕ} {A : Mat (n + 1)} (hA : IsSymplectic A)
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) {l : ℝ} (hl : l ≠ 0) :
    scaleM l A = Matrix.diagonal (fun i => if i = ie n then l else if i = jf n then l⁻¹ else 1) *
      A * Matrix.diagonal (fun j => if j = ie n then l⁻¹ else if j = jf n then l else 1) := by
  ext i j
  rw [mul_diagonal, diagonal_mul, scaleM_apply]
  by_cases hi : i = jf n
  · subst hi
    rw [row_f hA he]
    by_cases hj : j = jf n
    · subst hj; simp [hl]
    · by_cases hj' : j = ie n
      · subst hj'; simp
      · simp [hj, hj']
  · by_cases hj : j = ie n
    · subst hj
      rw [col_e he]
      by_cases hi' : i = ie n
      · subst hi'; simp [hl]
      · simp [hi, hi']
    · by_cases hi' : i = ie n
      · subst hi'
        by_cases hjf : j = jf n
        · subst hjf; simp; ring
        · simp [hj, hjf]
      · by_cases hjf : j = jf n
        · subst hjf; simp [hi, hi']; ring
        · simp [hi, hi', hj, hjf]

lemma scaleM_isSymplectic_of_ne {n : ℕ} {A : Mat (n + 1)} (hA : IsSymplectic A)
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) {l : ℝ} (hl : l ≠ 0) :
    IsSymplectic (scaleM l A) := by
  rw [scaleM_eq_conj hA he hl]
  have h1 := diagonal_isSymplectic
    (fun i : Fin (n + 1) ⊕ Fin (n + 1) => if i = ie n then l else if i = jf n then l⁻¹ else 1)
    (by
      intro k
      by_cases hk : k = Fin.last n
      · subst hk; simp [hl]
      · simp [hk])
  have h2 := diagonal_isSymplectic
    (fun i : Fin (n + 1) ⊕ Fin (n + 1) => if i = ie n then l⁻¹ else if i = jf n then l else 1)
    (by
      intro k
      by_cases hk : k = Fin.last n
      · subst hk; simp [hl]
      · simp [hk])
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ h1 hA) h2

lemma continuous_scaleM {n : ℕ} :
    Continuous fun p : ℝ × Mat (n + 1) => scaleM p.1 p.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [scaleM_apply]
  have hA : Continuous fun p : ℝ × Mat (n + 1) => p.2 i j :=
    (continuous_apply_apply i j).comp continuous_snd
  split_ifs
  · exact hA
  all_goals first
    | exact (continuous_fst.mul continuous_fst).mul hA
    | exact (continuous_fst.mul continuous_const).mul hA
    | exact (continuous_const.mul continuous_fst).mul hA
    | exact (continuous_const.mul continuous_const).mul hA

lemma scaleM_isSymplectic {n : ℕ} {A : Mat (n + 1)} (hA : IsSymplectic A)
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) (l : ℝ) :
    IsSymplectic (scaleM l A) := by
  have hc : Continuous fun l : ℝ => scaleM l A :=
    continuous_scaleM.comp (continuous_id.prodMk continuous_const)
  have hS : IsClosed {l : ℝ | scaleM l A * J (Fin (n + 1)) ℝ * (scaleM l A)ᵀ =
      J (Fin (n + 1)) ℝ} :=
    isClosed_eq ((hc.mul continuous_const).mul hc.matrix_transpose) continuous_const
  have hsub : ({0}ᶜ : Set ℝ) ⊆ {l : ℝ | scaleM l A * J (Fin (n + 1)) ℝ * (scaleM l A)ᵀ =
      J (Fin (n + 1)) ℝ} := fun l hl =>
    SymplecticGroup.mem_iff.mp (scaleM_isSymplectic_of_ne hA he hl)
  have := hS.closure_subset_iff.mpr hsub
  rw [closure_compl_singleton] at this
  exact SymplecticGroup.mem_iff.mpr (this (Set.mem_univ l))

lemma scaleM_one_left {n : ℕ} (A : Mat (n + 1)) : scaleM 1 A = A := by
  ext i j; simp [scaleM_apply]

lemma scaleM_one_right {n : ℕ} (l : ℝ) : scaleM l (1 : Mat (n + 1)) = 1 := by
  ext i j
  rw [scaleM_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h1 : i = jf n
    · simp [h1]
    · by_cases h2 : i = ie n
      · simp [h2]
      · simp [h1, h2]
  · simp [Matrix.one_apply, hij]

/-- The coordinate equivalence used by `ConleyZehnder.diamond`. -/
abbrev dEquiv (n' n'' : ℕ) :
    ((Fin n' ⊕ Fin n') ⊕ (Fin n'' ⊕ Fin n'')) ≃ (Fin (n' + n'') ⊕ Fin (n' + n'')) :=
  (Equiv.sumSumSumComm (Fin n') (Fin n') (Fin n'') (Fin n'')).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

@[simp] lemma castAdd_ne_last {n : ℕ} (b : Fin n) : Fin.castAdd 1 b ≠ Fin.last n := by
  intro h; have := congrArg Fin.val h; simp at this; omega

@[simp] lemma natAdd_zero_eq_last (n : ℕ) : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
  ext; simp

/-- The `Sp(2n)` block of a matrix on the coordinates other than `e, f`. -/
def blk {n : ℕ} (A : Mat (n + 1)) : Mat n :=
  A.submatrix (fun x => dEquiv n 1 (Sum.inl x)) (fun x => dEquiv n 1 (Sum.inl x))

lemma scaleM_zero {n : ℕ} {A : Mat (n + 1)} (hA : IsSymplectic A)
    (he : A *ᵥ Pi.single (ie n) 1 = Pi.single (ie n) 1) :
    scaleM 0 A = ConleyZehnder.diamond (blk A) (1 : Mat 1) := by
  ext i j
  obtain ⟨a, rfl⟩ := (dEquiv n 1).surjective i
  obtain ⟨b, rfl⟩ := (dEquiv n 1).surjective j
  change _ = Matrix.reindex (dEquiv n 1) (dEquiv n 1) (Matrix.fromBlocks (blk A) 0 0 1) _ _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, scaleM_apply]
  rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
    simp [blk, row_f hA he, col_e he, Matrix.one_apply, Fin.fin_one_eq_zero]

lemma blk_one (n : ℕ) : blk (1 : Mat (n + 1)) = 1 := by
  ext i j
  simp only [blk, Matrix.submatrix_apply, Matrix.one_apply, (dEquiv n 1).injective.eq_iff,
    Sum.inl.injEq]

theorem main (n : ℕ)
    (B : C(unitInterval, Mat (n + 1))) (hs : ∀ t, IsSymplectic (B t)) (h0 : B 0 = 1)
    (h1 : B 1 = 1)
    (he : ∀ t, B t *ᵥ Pi.single (Sum.inl (Fin.last n)) 1 = Pi.single (Sum.inl (Fin.last n)) 1) :
    ∃ B' : C(unitInterval, Mat n), (∀ t, IsSymplectic (B' t)) ∧ B' 0 = 1 ∧ B' 1 = 1 ∧
      ∃ Φ : C(unitInterval × unitInterval, Mat (n + 1)), (∀ t, Φ (0, t) = B t) ∧
        (∀ t, Φ (1, t) = ConleyZehnder.diamond (B' t) (1 : Mat 1)) ∧
        (∀ s t, IsSymplectic (Φ (s, t))) ∧ (∀ s, Φ (s, 0) = 1) ∧ ∀ s, Φ (s, 1) = 1 := by
  let B' : C(unitInterval, Mat n) :=
    ⟨fun t => blk (B t), continuous_pi fun i => continuous_pi fun j => by
      simp only [blk, Matrix.submatrix_apply]
      exact (continuous_apply_apply _ _).comp B.continuous⟩
  let Φ : C(unitInterval × unitInterval, Mat (n + 1)) :=
    ⟨fun p => scaleM (1 - (p.1 : ℝ)) (B p.2), continuous_scaleM.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
        (B.continuous.comp continuous_snd))⟩
  have hΦ : ∀ s t, Φ (s, t) = scaleM (1 - (s : ℝ)) (B t) := fun _ _ => rfl
  refine ⟨B', fun t => ?_, ?_, ?_, Φ, fun t => ?_, fun t => ?_, fun s t => ?_, fun s => ?_,
    fun s => ?_⟩
  · apply isSymplectic_left_of_diamond _ (1 : Mat 1)
    change IsSymplectic (ConleyZehnder.diamond (blk (B t)) 1)
    rw [← scaleM_zero (hs t) (he t)]
    exact scaleM_isSymplectic (hs t) (he t) 0
  · change blk (B 0) = 1; rw [h0, blk_one]
  · change blk (B 1) = 1; rw [h1, blk_one]
  · rw [hΦ]; simp [scaleM_one_left]
  · rw [hΦ]; simp only [Set.Icc.coe_one, sub_self]; exact scaleM_zero (hs t) (he t)
  · rw [hΦ]; exact scaleM_isSymplectic (hs t) (he t) _
  · rw [hΦ, h0, scaleM_one_right]
  · rw [hΦ, h1, scaleM_one_right]

end CRLK5

open CauchyRiemannIndex in
theorem solution (n : ℕ)
    (B : C(unitInterval, Mat (n + 1))) (hs : ∀ t, IsSymplectic (B t)) (h0 : B 0 = 1)
    (h1 : B 1 = 1)
    (he : ∀ t, B t *ᵥ Pi.single (Sum.inl (Fin.last n)) 1 = Pi.single (Sum.inl (Fin.last n)) 1) :
    ∃ B' : C(unitInterval, Mat n), (∀ t, IsSymplectic (B' t)) ∧ B' 0 = 1 ∧ B' 1 = 1 ∧
      ∃ Φ : C(unitInterval × unitInterval, Mat (n + 1)), (∀ t, Φ (0, t) = B t) ∧
        (∀ t, Φ (1, t) = ConleyZehnder.diamond (B' t) (1 : Mat 1)) ∧
        (∀ s t, IsSymplectic (Φ (s, t))) ∧ (∀ s, Φ (s, 0) = 1) ∧ ∀ s, Φ (s, 1) = 1 :=
  CRLK5.main n B hs h0 h1 he
