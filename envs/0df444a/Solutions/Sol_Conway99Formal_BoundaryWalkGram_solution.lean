-- Prove2me | solution 1 for Conway99Formal.BoundaryWalkGram.solution
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:25:14.371468+00:00
-- url     : https://prove2.me/submissions/04dd9fb0-f721-42c8-9768-e1c75fd12b14

import Definitions.Def_Conway99_Boundary_Walk_20261003

set_option autoImplicit false

namespace Conway99Formal.BoundaryWalkGram

open Matrix

variable {P O L : Type*} [Fintype P] [Fintype O] [Fintype L]
  [DecidableEq P] [DecidableEq O] [DecidableEq L]

private theorem ones_mul_transpose (X : Matrix P O ℤ) :
    ones P O * Xᵀ = ones P Unit * (e X)ᵀ := by
  ext i j
  simp [ones, e, Matrix.mul_apply, Finset.sum_mul]

private theorem ones_sandwich (X : Matrix P O ℤ) :
    X * ones O O * Xᵀ = e X * (e X)ᵀ := by
  have h : X * ones O O = e X * ones Unit O := by
    ext i j
    simp [ones, e, Matrix.mul_apply]
  rw [h, Matrix.mul_assoc]
  have h' : ones Unit O * Xᵀ = (e X)ᵀ := by
    ext i j
    simp [ones, e, Matrix.mul_apply]
  rw [h']

/-- The patch/outside P3 block determines the first boundary walk matrix. -/
theorem T_identity (AP : Matrix P P ℤ) (X : Matrix P O ℤ)
    (Y : Matrix O O ℤ) (NP : Matrix P L ℤ) (NO : Matrix O L ℤ)
    (hPO : AP * X + X * Y + X =
      2 • ones P O - NP * NOᵀ) :
    T X Y = 2 • (ones P Unit * (e X)ᵀ) -
      NP * (R X NO)ᵀ - AP * D X - D X := by
  have h := congrArg (fun M : Matrix P O ℤ => M * Xᵀ) hPO
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul] at h
  rw [ones_mul_transpose] at h
  simp only [D, R, T, Matrix.transpose_mul, Matrix.mul_assoc] at *
  linear_combination (norm := module) h

/-- The outside/outside P3 block determines the second boundary walk matrix. -/
theorem U_identity (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (NO : Matrix O L ℤ)
    (hOO : Xᵀ * X + Y * Y + Y =
      12 • (1 : Matrix O O ℤ) + 2 • ones O O - NO * NOᵀ) :
    U X Y = 12 • D X - T X Y + 2 • (e X * (e X)ᵀ) -
      R X NO * (R X NO)ᵀ - D X * D X := by
  have h := congrArg (fun M : Matrix O O ℤ => X * M * Xᵀ) hOO
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul] at h
  rw [ones_sandwich] at h
  simp only [D, R, T, U, Matrix.transpose_mul, Matrix.mul_assoc] at *
  linear_combination (norm := module) h

theorem T_symmetric (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hY : Yᵀ = Y) : (T X Y)ᵀ = T X Y := by
  simp [T, Matrix.transpose_mul, Matrix.mul_assoc, hY]

theorem T_nonnegative (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j)
    (i j : P) : 0 ≤ T X Y i j := by
  simp only [T, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (hX i b) (hY b a)
  · exact hX j a

theorem U_nonnegative (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hX : ∀ i j, 0 ≤ X i j) (hY : ∀ i j, 0 ≤ Y i j)
    (i j : P) : 0 ≤ U X Y i j := by
  simp only [U, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg (hX i b)
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (hY b c) (hY c a)
  · exact hX j a

private theorem even_symmetric_quadratic (x : O → ℤ) (Y : Matrix O O ℤ)
    (hY : ∀ a b, Y a b = Y b a) (hdiag : ∀ a, Y a a = 0) :
    Even (∑ b : O, (∑ a : O, x a * Y a b) * x b) := by
  classical
  have hz :
      (∑ p ∈ (Finset.univ : Finset O) ×ˢ Finset.univ,
        ((x p.2 * Y p.2 p.1 * x p.1 : ℤ) : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro ⟨a, b⟩ _
      dsimp
      rw [hY b a]
      have heq :
          ((x b * Y a b * x a : ℤ) : ZMod 2) =
            ((x a * Y a b * x b : ℤ) : ZMod 2) := by ring
      rw [heq, CharTwo.add_self_eq_zero]
    · intro ⟨a, b⟩ _ hf heq
      have hba : b = a := congrArg Prod.fst heq
      subst b
      simpa [hdiag] using hf
    · intro _ _
      simp
    · intro _ _
      rfl
  apply ZMod.intCast_eq_zero_iff_even.mp
  calc
    (((∑ b : O, (∑ a : O, x a * Y a b) * x b) : ℤ) : ZMod 2) =
        ∑ b : O, ∑ a : O,
          ((x a * Y a b * x b : ℤ) : ZMod 2) := by
            simp [Finset.sum_mul]
    _ = ∑ p ∈ (Finset.univ : Finset O) ×ˢ Finset.univ,
          ((x p.2 * Y p.2 p.1 * x p.1 : ℤ) : ZMod 2) := by
            rw [Finset.sum_product]
    _ = 0 := hz

theorem T_even_diagonal (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hY : Yᵀ = Y) (hdiag : ∀ a, Y a a = 0) (i : P) :
    Even (T X Y i i) := by
  have hs : ∀ a b, Y a b = Y b a := by
    intro a b
    have h := congrArg (fun M : Matrix O O ℤ => M b a) hY
    simpa using h
  convert even_symmetric_quadratic (fun a => X i a) Y hs hdiag using 1
  simp [T, Matrix.mul_apply]

theorem jointGram_eq_rows (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hY : Yᵀ = Y) :
    jointGram X Y = walkRows X Y * (walkRows X Y)ᵀ := by
  simp [jointGram, walkRows, Matrix.transpose_fromRows,
    Matrix.fromRows_mul_fromCols, D, T, U, Matrix.transpose_mul,
    hY, Matrix.mul_assoc]

theorem jointGram_posSemidef (X : Matrix P O ℤ) (Y : Matrix O O ℤ)
    (hY : Yᵀ = Y) :
    ((jointGram X Y).map (Int.castRingHom ℝ)).PosSemidef := by
  rw [jointGram_eq_rows X Y hY, Matrix.map_mul, Matrix.transpose_map]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose
      ((walkRows X Y).map (Int.castRingHom ℝ)))

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] lemma allOnes_apply {m n α : Type*} [One α] (i : m) (j : n) :
    allOnes m n α i j = 1 := rfl

theorem actual_compl_adj_eq (G : SimpleGraph V) [DecidableRel G.Adj] (α : Type*) [Ring α]
    [DecidableEq α] :
    Gᶜ.adjMatrix α = (of 1 : Matrix V V α) - 1 - G.adjMatrix α := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := α)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl α] at h
  linear_combination (norm := module) h

theorem actual_srg_A_sq {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [Ring α] [DecidableEq α] :
    (G.adjMatrix α) ^ 2
      = 12 • (1 : Matrix V V α) - G.adjMatrix α + 2 • (of 1 : Matrix V V α) := by
  have hm := h.matrix_eq (α := α)
  rw [actual_compl_adj_eq G α] at hm
  rw [hm]; module


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma actual_split_sum (f : V → ℤ) :
    (∑ v : V, f v) = f r + (∑ u : actualLocT G r, f u.1) +
      (∑ w : actualFarT G r, f w.1) := by
  have hr : r ∉ actualLocF G r := by simp [actualLocF]
  have hroot : (∑ v ∈ insert r (actualLocF G r), f v) =
      f r + ∑ v ∈ actualLocF G r, f v := by
    rw [Finset.sum_insert hr]
  have hloc : (∑ v ∈ actualLocF G r, f v) =
      ∑ u : actualLocT G r, f u.1 :=
    Finset.sum_subtype (actualLocF G r) (fun _ => Iff.rfl) f
  have hfar : (∑ v ∈ actualFarF G r, f v) =
      ∑ w : actualFarT G r, f w.1 :=
    Finset.sum_subtype (actualFarF G r) (fun _ => Iff.rfl) f
  calc
    (∑ v : V, f v) = (∑ v ∈ insert r (actualLocF G r), f v) +
        (∑ v ∈ actualFarF G r, f v) := by
      simpa [actualFarF] using
        (Finset.sum_add_sum_compl (insert r (actualLocF G r)) f).symm
    _ = _ := by rw [hroot, hloc, hfar]

private lemma actual_far_not_root (x : actualFarT G r) : x.1 ≠ r ∧ ¬ G.Adj r x.1 := by
  have hx : x.1 ∉ insert r (actualLocF G r) :=
    (Finset.mem_sdiff.mp x.2).2
  simp only [Finset.mem_insert, not_or] at hx
  exact ⟨hx.1, by simpa [actualLocF] using hx.2⟩

private lemma actual_far_root_entry (x : actualFarT G r) :
    G.adjMatrix ℤ x.1 r = 0 := by
  have hx := (actual_far_not_root G r x).2
  simp [SimpleGraph.adjMatrix_apply, G.adj_comm, hx]

private lemma actual_square_split (x : actualFarT G r) (y : V) :
    (∑ v : V, G.adjMatrix ℤ x.1 v * G.adjMatrix ℤ v y) =
      (∑ u : actualLocT G r,
        G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ w : actualFarT G r,
        G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y) := by
  have hs := actual_split_sum G r (fun v => G.adjMatrix ℤ x.1 v * G.adjMatrix ℤ v y)
  rw [actual_far_root_entry G r x, zero_mul, zero_add] at hs
  exact hs

private lemma actual_square_entry (h : G.IsSRGWith 99 14 1 2) (x y : V) :
    (∑ v : V, G.adjMatrix ℤ x v * G.adjMatrix ℤ v y) +
      G.adjMatrix ℤ x y = (if x = y then 12 else 0) + 2 := by
  have hh := congrArg (fun M : Matrix V V ℤ => M x y) (actual_srg_A_sq h ℤ)
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at hh
  simp [Matrix.one_apply, Matrix.of_apply] at hh ⊢
  omega

theorem transport (h : G.IsSRGWith 99 14 1 2) :
    actualAFar G r * actualNReg G r +
      actualNReg G r * actualMMate G r + actualNReg G r =
      2 • allOnes (actualFarT G r) (actualLocT G r) ℤ := by
  ext x y
  have hxy : x.1 ≠ y.1 := by
    intro e
    have hy : G.Adj r y.1 := (G.mem_neighborFinset r y.1).mp y.2
    exact (actual_far_not_root G r x).2 (e.symm ▸ hy)
  have hs := actual_square_split G r x y.1
  have he := actual_square_entry G h x.1 y.1
  simp only [if_neg hxy, zero_add] at he
  change ((∑ w : actualFarT G r,
      G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y.1) +
      (∑ u : actualLocT G r,
        G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1)) +
      G.adjMatrix ℤ x.1 y.1 = 2
  omega

theorem actual_far_quadratic (h : G.IsSRGWith 99 14 1 2) :
    actualAFar G r ^ 2 + actualAFar G r +
      actualNReg G r * (actualNReg G r)ᵀ =
      12 • (1 : Matrix (actualFarT G r) (actualFarT G r) ℤ) +
        2 • allOnes (actualFarT G r) (actualFarT G r) ℤ := by
  ext x y
  have hs := actual_square_split G r x y.1
  have he := actual_square_entry G h x.1 y.1
  simp only [Subtype.coe_inj] at he
  simp only [sq, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, allOnes_apply, actualAFar, actualNReg,
    Matrix.submatrix_apply, Matrix.transpose_apply] at ⊢
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at ⊢
  have hsym (u : actualLocT G r) :
      G.adjMatrix ℤ y.1 u.1 = G.adjMatrix ℤ u.1 y.1 := by
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  simp_rw [hsym]
  change (∑ w : actualFarT G r,
      G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y.1) +
    G.adjMatrix ℤ x.1 y.1 +
    (∑ u : actualLocT G r,
      G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1) =
      (if x = y then 12 else 0) + 2
  omega

variable {F : Type*} [Fintype F] [DecidableEq F]

private theorem split_far_sum (S : Finset F) (f : F → ℤ) :
    (∑ k : F, f k) = (∑ p : Patch S, f p.1) +
      (∑ o : Outside S, f o.1) := by
  have hp : (∑ k ∈ S, f k) = ∑ p : Patch S, f p.1 :=
    Finset.sum_subtype S (fun _ => Iff.rfl) f
  have ho : (∑ k ∈ Finset.univ \ S, f k) = ∑ o : Outside S, f o.1 :=
    Finset.sum_subtype (Finset.univ \ S) (fun _ => Iff.rfl) f
  calc
    (∑ k : F, f k) = (∑ k ∈ S, f k) +
        (∑ k ∈ Finset.univ \ S, f k) := by
      simpa using (Finset.sum_add_sum_compl S f).symm
    _ = _ := by rw [hp, ho]

/-- The PO block of one far P3 equation, with no independent boundary witness. -/
theorem patch_outside_P3 {L : Type*} [Fintype L]
    (A : Matrix F F ℤ) (N : Matrix F L ℤ) (S : Finset F)
    (hP3 : A * A + A + N * Nᵀ =
      12 • (1 : Matrix F F ℤ) + 2 • ones F F) :
    patchAdj A S * boundaryIncidence A S +
      boundaryIncidence A S * outsideAdj A S + boundaryIncidence A S =
      2 • ones (Patch S) (Outside S) -
        patchNear N S * (outsideNear N S)ᵀ := by
  ext p o
  have hne : (p.1 : F) ≠ o.1 := by
    intro e
    have hp : o.1 ∈ S := e ▸ p.2
    exact (Finset.mem_sdiff.mp o.2).2 hp
  have he := congrArg (fun M : Matrix F F ℤ => M p.1 o.1) hP3
  have he' : (∑ k : F, A p.1 k * A k o.1) + A p.1 o.1 +
      (∑ l : L, N p.1 l * N o.1 l) = 2 := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.one_apply, ones, Matrix.of_apply] at he
    simpa [hne] using he
  rw [split_far_sum S (fun k => A p.1 k * A k o.1)] at he'
  simp only [patchAdj, boundaryIncidence, outsideAdj, patchNear,
    outsideNear, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply,
    id_eq] at ⊢
  simp only [ones, Matrix.of_apply, nsmul_eq_mul, mul_one] at ⊢
  omega

/-- The OO block of the same far P3 equation. -/
theorem outside_outside_P3 {L : Type*} [Fintype L]
    (A : Matrix F F ℤ) (N : Matrix F L ℤ) (S : Finset F)
    (hA : Aᵀ = A)
    (hP3 : A * A + A + N * Nᵀ =
      12 • (1 : Matrix F F ℤ) + 2 • ones F F) :
    (boundaryIncidence A S)ᵀ * boundaryIncidence A S +
      outsideAdj A S * outsideAdj A S + outsideAdj A S =
      12 • (1 : Matrix (Outside S) (Outside S) ℤ) +
        2 • ones (Outside S) (Outside S) -
          outsideNear N S * (outsideNear N S)ᵀ := by
  ext i j
  have he := congrArg (fun M : Matrix F F ℤ => M i.1 j.1) hP3
  have he' : (∑ k : F, A i.1 k * A k j.1) + A i.1 j.1 +
      (∑ l : L, N i.1 l * N j.1 l) =
        (if i = j then 12 else 0) + 2 := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.one_apply, ones, Matrix.of_apply] at he
    simpa [Subtype.coe_inj] using he
  rw [split_far_sum S (fun k => A i.1 k * A k j.1)] at he'
  have hs (p : Patch S) : A i.1 p.1 = A p.1 i.1 := by
    have h := congrArg (fun M : Matrix F F ℤ => M p.1 i.1) hA
    simpa using h
  simp_rw [hs] at he'
  simp only [boundaryIncidence, outsideAdj, outsideNear,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, id_eq,
    Matrix.one_apply] at ⊢
  simp only [ones, Matrix.of_apply, nsmul_eq_mul, mul_one, mul_ite,
    mul_zero] at ⊢
  linear_combination (norm := module) he'

theorem boundary_conditions_proof {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (h : G.IsSRGWith 99 14 1 2)
    (S : Finset (actualFarT G r)) : actualConditions G r S := by
  let A := actualAFar G r
  let N := actualNReg G r
  let AP := patchAdj A S
  let X := boundaryIncidence A S
  let Y := outsideAdj A S
  let NP := patchNear N S
  let NO := outsideNear N S
  have hP3 : A * A + A + N * Nᵀ =
      12 • (1 : Matrix (actualFarT G r) (actualFarT G r) ℤ) +
        2 • ones (actualFarT G r) (actualFarT G r) := by
    simpa only [sq, allOnes, ones] using actual_far_quadratic G r h
  have hA : Aᵀ = A := by
    ext i j
    simp [A, actualAFar, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hPO := patch_outside_P3 A N S hP3
  have hOO := outside_outside_P3 A N S hA hP3
  have hYsym : Yᵀ = Y := by
    ext i j
    have h := congrArg (fun M : Matrix (actualFarT G r) (actualFarT G r) ℤ => M i.1 j.1) hA
    change A j.1 i.1 = A i.1 j.1
    simpa using h
  have hYdiag : ∀ i, Y i i = 0 := by
    intro i
    change G.adjMatrix ℤ i.1.1 i.1.1 = 0
    simp [SimpleGraph.adjMatrix_apply]
  have hXnonneg : ∀ i j, 0 ≤ X i j := by
    intro i j
    change 0 ≤ G.adjMatrix ℤ i.1.1 j.1.1
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hYnonneg : ∀ i j, 0 ≤ Y i j := by
    intro i j
    change 0 ≤ G.adjMatrix ℤ i.1.1 j.1.1
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  change T X Y = 2 • (ones (Patch S) Unit * (e X)ᵀ) -
      NP * (R X NO)ᵀ - AP * D X - D X ∧
    U X Y = 12 • D X - T X Y + 2 • (e X * (e X)ᵀ) -
      R X NO * (R X NO)ᵀ - D X * D X ∧
    (T X Y)ᵀ = T X Y ∧
    (∀ i j, 0 ≤ T X Y i j) ∧
    (∀ i, Even (T X Y i i)) ∧
    (∀ i j, 0 ≤ U X Y i j) ∧
    ((jointGram X Y).map (Int.castRingHom ℝ)).PosSemidef
  refine ⟨T_identity AP X Y NP NO hPO, U_identity X Y NO hOO,
    T_symmetric X Y hYsym, ?_, ?_, ?_, jointGram_posSemidef X Y hYsym⟩
  · intro i j
    exact T_nonnegative X Y hXnonneg hYnonneg i j
  · intro i
    exact T_even_diagonal X Y hYsym hYdiag i
  · intro i j
    exact U_nonnegative X Y hXnonneg hYnonneg i j

#print axioms T_identity
#print axioms U_identity
#print axioms T_symmetric
#print axioms T_nonnegative
#print axioms U_nonnegative
#print axioms T_even_diagonal
#print axioms jointGram_eq_rows
#print axioms jointGram_posSemidef
#print axioms actual_compl_adj_eq
#print axioms actual_srg_A_sq
#print axioms allOnes_apply
#print axioms transport
#print axioms actual_far_quadratic
#print axioms patch_outside_P3
#print axioms outside_outside_P3
#print axioms boundary_conditions_proof

end Conway99Formal.BoundaryWalkGram

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (h : G.IsSRGWith 99 14 1 2)
    (S : Finset (Conway99Formal.BoundaryWalkGram.actualFarT G r)) :
    Conway99Formal.BoundaryWalkGram.actualConditions G r S := by
  exact Conway99Formal.BoundaryWalkGram.boundary_conditions_proof G r h S

#print axioms solution
