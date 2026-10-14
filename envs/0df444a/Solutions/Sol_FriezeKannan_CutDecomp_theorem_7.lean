-- Prove2me | solution 1 for FriezeKannan.CutDecomp.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:08:53.624131+00:00
-- url     : https://prove2.me/submissions/cbc4e986-65e6-4975-8d0d-80332eefb619

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

set_option autoImplicit false

section FKAux

open FriezeKannan.CutDecomp

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

lemma fkaux_frobNorm_sq (M : Matrix R C ℝ) : frobNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  unfold frobNorm
  apply Real.sq_sqrt
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma fkaux_drop_eq (W : Matrix R C ℝ) (S : Finset R) (T : Finset C) (hS : S.Nonempty)
    (hT : T.Nonempty) :
    frobNorm (W - cutMatrix S T (blockSum W S T / ((S.card : ℝ) * T.card))) ^ 2
        - frobNorm W ^ 2 = -(blockSum W S T) ^ 2 / ((S.card : ℝ) * T.card) := by
  set d : ℝ := blockSum W S T / ((S.card : ℝ) * T.card) with hd
  have hn : ((S.card : ℝ) * T.card) ≠ 0 := by
    have h1 : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have h2 : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    positivity
  rw [fkaux_frobNorm_sq, fkaux_frobNorm_sq, ← Finset.sum_sub_distrib]
  have h1 : ∀ i : R, (∑ j, (W - cutMatrix S T d) i j ^ 2) - ∑ j, W i j ^ 2
      = if i ∈ S then ∑ j ∈ T, ((W i j - d) ^ 2 - W i j ^ 2) else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      have : ∀ j : C, ((W - cutMatrix S T d) i j ^ 2 - W i j ^ 2)
          = if j ∈ T then ((W i j - d) ^ 2 - W i j ^ 2) else 0 := by
        intro j
        by_cases hj : j ∈ T
        · simp [cutMatrix, hi, hj]
        · simp [cutMatrix, hi, hj]
      simp_rw [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      simp [cutMatrix, hi]
  simp_rw [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : ∑ i ∈ S, ∑ j ∈ T, ((W i j - d) ^ 2 - W i j ^ 2)
      = ∑ i ∈ S, ∑ j ∈ T, (d ^ 2 - 2 * d * W i j) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [h2]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have h3 : ∑ i ∈ S, ∑ j ∈ T, W i j = blockSum W S T := rfl
  rw [h3, hd]
  field_simp
  ring

lemma fkaux_drop_le (A W : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (S : Finset R) (T : Finset C)
    (h : ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A < |blockSum W S T|) :
    frobNorm (W - cutMatrix S T (blockSum W S T / ((S.card : ℝ) * T.card))) ^ 2
        - frobNorm W ^ 2 ≤ -ε ^ 2 * frobNorm A ^ 2 := by
  have hF : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  have hpos : 0 ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A := by positivity
  have hb : 0 < |blockSum W S T| := lt_of_le_of_lt hpos h
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl
    simp [blockSum] at hb
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl
    simp [blockSum] at hb
  rw [fkaux_drop_eq W S T hSne hTne]
  have h1 : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have h2 : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hn : (0 : ℝ) < (S.card : ℝ) * T.card := by positivity
  have hsq : (ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ^ 2 < (blockSum W S T) ^ 2 := by
    rw [← sq_abs (blockSum W S T)]
    exact pow_lt_pow_left₀ h hpos (by norm_num)
  have hexp : (ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ^ 2
      = ε ^ 2 * ((S.card : ℝ) * T.card) * frobNorm A ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
  rw [hexp] at hsq
  have h4 : ε ^ 2 * frobNorm A ^ 2 ≤ (blockSum W S T) ^ 2 / ((S.card : ℝ) * T.card) := by
    rw [le_div_iff₀ hn]; nlinarith
  rw [neg_div]
  linarith

lemma fkaux_step (A : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ)
    (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ)
    (hinv : frobNorm (A - cutSum Rs Cs d) ^ 2 ≤ (1 - ε ^ 2 * t) * frobNorm A ^ 2) :
    (∀ (S : Finset R) (T : Finset C),
        |blockSum (A - cutSum Rs Cs d) S T|
          ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ∨
      ∃ (S : Finset R) (T : Finset C) (d' : ℝ),
        frobNorm (A - (cutSum Rs Cs d + cutMatrix S T d')) ^ 2
          ≤ (1 - ε ^ 2 * (t + 1)) * frobNorm A ^ 2 := by
  by_cases h : ∀ (S : Finset R) (T : Finset C),
      |blockSum (A - cutSum Rs Cs d) S T| ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨S, T, hST⟩ := h
    refine ⟨S, T, blockSum (A - cutSum Rs Cs d) S T / ((S.card : ℝ) * T.card), ?_⟩
    have := fkaux_drop_le A (A - cutSum Rs Cs d) ε hε S T hST
    have e : A - (cutSum Rs Cs d + cutMatrix S T (blockSum (A - cutSum Rs Cs d) S T
        / ((S.card : ℝ) * T.card))) = (A - cutSum Rs Cs d) - cutMatrix S T
        (blockSum (A - cutSum Rs Cs d) S T / ((S.card : ℝ) * T.card)) := by
      rw [sub_add_eq_sub_sub]
    rw [e]
    nlinarith

lemma fkaux_cutSum_snoc {t : ℕ} (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ)
    (S : Finset R) (T : Finset C) (d' : ℝ) :
    cutSum (Fin.snoc (α := fun _ => Finset R) Rs S) (Fin.snoc (α := fun _ => Finset C) Cs T)
      (Fin.snoc (α := fun _ => ℝ) d d') = cutSum Rs Cs d + cutMatrix S T d' := by
  unfold cutSum
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end FKAux

open FriezeKannan.CutDecomp in
theorem solution {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
      ∃ (Rs : Fin s → Finset R) (Cs : Fin s → Finset C) (d : Fin s → ℝ),
        ∀ (S : Finset R) (T : Finset C),
          |blockSum (A - cutSum Rs Cs d) S T|
            ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A := by
  have hF : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  rcases hF.eq_or_lt with h0 | hpos
  · -- A = 0
    refine ⟨0, by rw [Nat.cast_zero]; positivity, fun i => ∅, fun j => ∅, fun _ => 0, ?_⟩
    intro S T
    have hcs : cutSum (R := R) (C := C) (fun i : Fin 0 => (∅ : Finset R))
        (fun j : Fin 0 => (∅ : Finset C)) (fun _ => 0) = 0 := by
      simp [cutSum]
    rw [hcs, sub_zero, ← h0, mul_zero]
    have hA : A = 0 := by
      have h1 : frobNorm A ^ 2 = 0 := by rw [← h0]; norm_num
      rw [fkaux_frobNorm_sq] at h1
      ext i j
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))).1 h1 i (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (A i j))).1 h2 j (Finset.mem_univ _)
      simpa using h3
    subst hA
    simp [blockSum]
  · have hbound : ∀ t : ℕ, ∀ (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ),
        frobNorm (A - cutSum Rs Cs d) ^ 2 ≤ (1 - ε ^ 2 * t) * frobNorm A ^ 2 →
        (t : ℝ) ≤ 1 / ε ^ 2 := by
      intro t Rs Cs d h
      have h1 : 0 ≤ frobNorm (A - cutSum Rs Cs d) ^ 2 := sq_nonneg _
      have h2 : 0 < frobNorm A ^ 2 := by positivity
      have h3 : 0 ≤ 1 - ε ^ 2 * t := by
        by_contra hneg
        push_neg at hneg
        nlinarith
      have hε2 : 0 < ε ^ 2 := by positivity
      rw [le_div_iff₀ hε2]
      linarith
    have key : ∀ t : ℕ,
        (∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
          ∃ (Rs : Fin s → Finset R) (Cs : Fin s → Finset C) (d : Fin s → ℝ),
            ∀ (S : Finset R) (T : Finset C),
              |blockSum (A - cutSum Rs Cs d) S T|
                ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ∨
        ∃ (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ),
          frobNorm (A - cutSum Rs Cs d) ^ 2 ≤ (1 - ε ^ 2 * t) * frobNorm A ^ 2 := by
      intro t
      induction t with
      | zero =>
        right
        refine ⟨fun i => ∅, fun j => ∅, fun _ => 0, ?_⟩
        have hcs : cutSum (R := R) (C := C) (fun i : Fin 0 => (∅ : Finset R))
            (fun j : Fin 0 => (∅ : Finset C)) (fun _ => 0) = 0 := by
          simp [cutSum]
        rw [hcs, sub_zero]
        simp
      | succ t ih =>
        rcases ih with h | ⟨Rs, Cs, d, hinv⟩
        · exact Or.inl h
        · rcases fkaux_step A ε hε t Rs Cs d hinv with h | ⟨S, T, d', hnew⟩
          · exact Or.inl ⟨t, hbound t Rs Cs d hinv, Rs, Cs, d, h⟩
          · right
            refine ⟨Fin.snoc (α := fun _ => Finset R) Rs S,
              Fin.snoc (α := fun _ => Finset C) Cs T, Fin.snoc (α := fun _ => ℝ) d d', ?_⟩
            rw [fkaux_cutSum_snoc]
            push_cast
            exact hnew
    rcases key (⌊1 / ε ^ 2⌋₊ + 1) with h | ⟨Rs, Cs, d, hinv⟩
    · exact h
    · exfalso
      have := hbound _ Rs Cs d hinv
      push_cast at this
      have h2 := Nat.lt_floor_add_one (1 / ε ^ 2)
      linarith
