-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.KP.lemmaSMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:26.565801+00:00
-- url     : https://prove2.me/submissions/498c2fe0-9c12-44fb-a91d-3c00c47161ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LemmaSMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.flipOneThree.Pf.KP
open Module
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
private theorem smt_unit {s ρ : ℕ} (E : Matrix (Fin s) (Fin ρ) O) (C : Matrix (Fin ρ) (Fin s) O)
    (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) : IsUnit (1 - E * C).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hE0 : E.map (IsLocalRing.residue O) = 0 := by
    ext i j
    simpa [Matrix.map_apply, IsLocalRing.residue_eq_zero_iff] using hE i j
  have h : (RingHom.mapMatrix (IsLocalRing.residue O)) (1 - E * C) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hE0, Matrix.zero_mul, sub_zero]
  rw [h, Matrix.det_one]
  exact one_ne_zero
private theorem smt_block {s ρ : ℕ} (z1 z2 : O) (E : Matrix (Fin s) (Fin ρ) O)
    (C : Matrix (Fin ρ) (Fin s) O) (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) :
    ∃ M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O,
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) ((z1 * z2) • E) C
        (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M =
      (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O) := by
  have hU := smt_unit E C hE
  have hV : IsUnit (1 - C * E).det := by rw [Matrix.det_one_sub_mul_comm]; exact hU
  have hUi : (1 - E * C) * (1 - E * C)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hVi : (1 - C * E) * (1 - C * E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hV
  refine ⟨Matrix.fromBlocks (z2 • (1 - E * C)⁻¹) (-(z1 * z2) • (E * (1 - C * E)⁻¹))
    (-(C * (1 - E * C)⁻¹)) (z1 • (1 - C * E)⁻¹), ?_⟩
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (z1 * z2) • (1 : Matrix (Fin s) (Fin s) O) = (z1 * z2) • ((1 - E * C) * (1 - E * C)⁻¹) := by
      rw [hUi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.mul_assoc, smul_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul, neg_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul]
    module
  · have e : (z1 * z2) • (1 : Matrix (Fin ρ) (Fin ρ) O) = (z1 * z2) • ((1 - C * E) * (1 - C * E)⁻¹) := by
      rw [hVi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc, smul_smul, neg_smul]
    module
end Formalism.MainNotions.flipOneThree.Pf.KP
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
open Module
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.KP
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O) :
  ∃ (r s : ℕ), r + s = σ ∧
    (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O), P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
    (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O) (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'') (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O)) := by
  classical
  have hz0 : z1 * z2 ≠ 0 := mul_ne_zero h1 h2
  have key : ∀ (n : ℕ) (N : Matrix (Fin n) (Fin ρ) O), ∃ (r s : ℕ), r + s = n ∧
      (∃ (P : Matrix (Fin r) (Fin n) O) (Q : Matrix (Fin ρ) (Fin r) O),
        P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
      (∃ (P' : Matrix (Fin s) (Fin n) O) (P'' : Matrix (Fin n) (Fin s) O), P' * P'' = 1 ∧
        ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, (P' * N) i j = z1 * z2 * e) := by
    intro n
    induction n with
    | zero =>
      intro N
      refine ⟨0, 0, rfl, ⟨0, 0, ?_⟩, ⟨0, 0, ?_, fun i => i.elim0⟩⟩
      · ext i; exact i.elim0
      · ext i; exact i.elim0
    | succ n ih =>
      intro N
      by_cases hall : ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, N i j = z1 * z2 * e
      · refine ⟨0, n + 1, by omega, ⟨0, 0, ?_⟩, ⟨1, 1, Matrix.one_mul 1, ?_⟩⟩
        · ext i; exact i.elim0
        · intro i j; rw [Matrix.one_mul]; exact hall i j
      obtain ⟨ia, hia⟩ := not_forall.mp hall
      obtain ⟨ja, hna⟩ := not_forall.mp hia
      obtain ⟨⟨i0, j0⟩, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1) × Fin ρ))
        (fun p => IsDiscreteValuationRing.addVal O (N p.1 p.2)) ⟨(ia, ja), Finset.mem_univ _⟩
      have hdiv : ∀ p : Fin (n + 1) × Fin ρ, N i0 j0 ∣ N p.1 p.2 := fun p =>
        (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin p (Finset.mem_univ _))
      have haz : N i0 j0 ∣ z1 * z2 := by
        by_contra hnd
        rcases le_total (IsDiscreteValuationRing.addVal O (N i0 j0))
            (IsDiscreteValuationRing.addVal O (z1 * z2)) with h | h
        · exact hnd ((IsDiscreteValuationRing.addVal_le_iff_dvd).mp h)
        · obtain ⟨e, he⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
          have hem : e ∈ IsLocalRing.maximalIdeal O := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            rintro ⟨u, rfl⟩
            exact hnd ⟨↑u⁻¹, by rw [he, mul_assoc, Units.mul_inv, mul_one]⟩
          apply hna
          obtain ⟨b, hb⟩ : N i0 j0 ∣ N ia ja := hdiv (ia, ja)
          exact ⟨e * b, Ideal.mul_mem_right _ _ hem, by rw [hb, he, mul_assoc]⟩
      obtain ⟨t, ht⟩ := haz
      choose f hf using hdiv
      have hf' : ∀ i l, N i l = N i0 j0 * f (i, l) := fun i l => hf (i, l)
      have ha0 : N i0 j0 ≠ 0 := by
        intro h0; apply hz0; rw [ht, h0, zero_mul]
      have hf00 : f (i0, j0) = 1 := by
        apply mul_left_cancel₀ ha0
        rw [mul_one]; exact (hf' i0 j0).symm
      let N1 : Matrix (Fin n) (Fin ρ) O :=
        Matrix.of fun k l => N (i0.succAbove k) l - f (i0.succAbove k, j0) * N i0 l
      obtain ⟨r1, s1, hrs, ⟨P1, Q1, hPQ⟩, ⟨P1', P1'', hP1, hgood⟩⟩ := ih N1
      let S : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun k i =>
        (if i = i0.succAbove k then 1 else 0) - (if i = i0 then f (i0.succAbove k, j0) else 0)
      let Em : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i k => if i = i0.succAbove k then 1 else 0
      let Ei : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ i => if i = i0 then t else 0
      let ej : Matrix (Fin ρ) (Fin 1) O := Matrix.of fun l _ => if l = j0 then 1 else 0
      let dd : Matrix (Fin 1) (Fin ρ) O := Matrix.of fun _ l => f (i0, l)
      let Q1' : Matrix (Fin ρ) (Fin r1) O := Q1 - ej * (dd * Q1)
      have hSN : S * N = N1 := by
        ext k l
        simp [S, N1, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]
      have hSE : S * Em = 1 := by
        ext k k'
        have hne : i0 ≠ i0.succAbove k' := Fin.ne_succAbove i0 k'
        have hne' : i0.succAbove k' ≠ i0 := Fin.succAbove_ne i0 k'
        simp only [S, Em, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
          one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply]
        simp [hne, hne', Fin.succAbove_right_inj]
      have hrow : Ei * N = (z1 * z2) • dd := by
        ext i l
        simp [Ei, dd, Matrix.mul_apply, ite_mul]
        rw [hf' i0 l, ht]; ring
      have hdd : dd * ej = 1 := by
        ext i j
        fin_cases i; fin_cases j
        simp [dd, ej, Matrix.mul_apply, hf00]
      have hN1e : N1 * ej = 0 := by
        ext k j
        simp [N1, ej, Matrix.mul_apply]
        rw [hf' (i0.succAbove k) j0]; ring
      have hblocks : Matrix.fromRows Ei (P1 * S) * N * Matrix.fromCols ej Q1' =
          (z1 * z2) • (1 : Matrix (Fin 1 ⊕ Fin r1) (Fin 1 ⊕ Fin r1) O) := by
        rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
          Matrix.fromBlocks_smul, smul_zero, smul_zero, Matrix.fromBlocks_inj]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrow, Matrix.smul_mul, hdd]
        · rw [hrow, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc dd ej, hdd,
            Matrix.one_mul, sub_self]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_assoc, hN1e, Matrix.mul_zero]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_sub, ← Matrix.mul_assoc (P1 * N1) ej,
            Matrix.mul_assoc P1 N1 ej, hN1e, Matrix.mul_zero, Matrix.zero_mul, sub_zero, hPQ]
      refine ⟨1 + r1, s1, by omega, ⟨(Matrix.fromRows Ei (P1 * S)).submatrix finSumFinEquiv.symm id,
        (Matrix.fromCols ej Q1').submatrix id finSumFinEquiv.symm, ?_⟩, ⟨P1' * S, Em * P1'', ?_, ?_⟩⟩
      · rw [← Matrix.submatrix_id_id N, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
          ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hblocks]
        ext i j
        simp [Matrix.one_apply]
      · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S Em, hSE, Matrix.one_mul, hP1]
      · intro i j
        rw [Matrix.mul_assoc, hSN]
        exact hgood i j
  obtain ⟨r, s, hrs, hP, P', P'', hP', hg⟩ := key σ N
  refine ⟨r, s, hrs, hP, P', P'', ?_⟩
  choose E hEm hE using hg
  obtain ⟨M, hM⟩ := smt_block z1 z2 (Matrix.of E) (B * P'') (fun i j => hEm i j)
  refine ⟨M, hP', ?_⟩
  have hPN : P' * N = (z1 * z2) • Matrix.of E := by
    ext i j
    simp [hE i j]
  rw [hPN]
  exact hM
end Formalism.MainNotions.flipOneThree.Pf.KP
