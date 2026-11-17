-- Prove2me | solution 1 for BaconThesis.Commutant.lemma_7_3_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:06:51.773962+00:00
-- url     : https://prove2.me/submissions/a10b774e-710e-455d-ae6c-714142410346

import Mathlib
import Definitions.Def_BaconThesis_Commutant_blockC
import Definitions.Def_BaconThesis_Commutant_algebraA
import Definitions.Def_BaconThesis_Commutant_irrepProj
import Definitions.Def_BaconThesis_Commutant_blockA

open scoped Kronecker

namespace BaconThesis.Commutant.Sol_lemma_7_3_1

open BaconThesis.Commutant

section aux

variable {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] {n d : 𝒥 → ℕ}

local notation "Idx" => (Σ J : 𝒥, Fin (n J) × Fin (d J))

private lemma blockA_mul_apply (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ)
    (M : Matrix Idx Idx ℂ) (J : 𝒥) (l : Fin (n J)) (m : Fin (d J)) (q : Idx) :
    (blockA n d X * M) ⟨J, (l, m)⟩ q = ∑ m2, X J m m2 * M ⟨J, (l, m2)⟩ q := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single l]
    · simp [blockA, Matrix.blockDiagonal'_apply_eq]
    · intro l2 _ hl
      simp [blockA, Matrix.blockDiagonal'_apply_eq, Ne.symm hl]
    · simp
  · intro J2 _ hJ
    simp [blockA, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hJ)]
  · simp

private lemma mul_blockA_apply (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ)
    (M : Matrix Idx Idx ℂ) (p : Idx) (J : 𝒥) (l : Fin (n J)) (m : Fin (d J)) :
    (M * blockA n d X) p ⟨J, (l, m)⟩ = ∑ m2, M p ⟨J, (l, m2)⟩ * X J m2 m := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single l]
    · simp [blockA, Matrix.blockDiagonal'_apply_eq]
    · intro l2 _ hl
      simp [blockA, Matrix.blockDiagonal'_apply_eq, hl]
    · simp
  · intro J2 _ hJ
    simp [blockA, Matrix.blockDiagonal'_apply_ne _ _ _ hJ]
  · simp

private lemma blockC_apply_same (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) (J : 𝒥)
    (l l' : Fin (n J)) (m m' : Fin (d J)) :
    blockC n d Y ⟨J, (l, m)⟩ ⟨J, (l', m')⟩ = Y J l l' * if m = m' then 1 else 0 := by
  simp [blockC, Matrix.blockDiagonal'_apply_eq, Matrix.one_apply]

private lemma blockC_apply_ne (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) {J J' : 𝒥}
    (h : J ≠ J') (x : Fin (n J) × Fin (d J)) (y : Fin (n J') × Fin (d J')) :
    blockC n d Y ⟨J, x⟩ ⟨J', y⟩ = 0 := by
  simp [blockC, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- The commutant of `⊕ I ⊗ M_{d_J}` is `⊕ M_{n_J} ⊗ I`. -/
private lemma eq_blockC_of_commute (hd : ∀ J, 0 < d J) (M : Matrix Idx Idx ℂ)
    (hM : ∀ X, blockA n d X * M = M * blockA n d X) :
    M = blockC n d fun J l l' => M ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩ := by
  have key : ∀ (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ) (J : 𝒥) (l : Fin (n J))
      (m : Fin (d J)) (J' : 𝒥) (l' : Fin (n J')) (m' : Fin (d J')),
      ∑ m2, X J m m2 * M ⟨J, (l, m2)⟩ ⟨J', (l', m')⟩ =
        ∑ m2, M ⟨J, (l, m)⟩ ⟨J', (l', m2)⟩ * X J' m2 m' := by
    intro X J l m J' l' m'
    rw [← blockA_mul_apply, ← mul_blockA_apply, hM]
  refine Matrix.ext fun ⟨J, l, m⟩ ⟨J', l', m'⟩ => ?_
  by_cases hJ : J = J'
  · subst hJ
    refine Eq.trans ?_ (blockC_apply_same _ J l l' m m').symm
    by_cases hm : m = m'
    · subst hm
      have := key (Pi.single J (Matrix.single m ⟨0, hd J⟩ 1)) J l m J l' ⟨0, hd J⟩
      simp [Matrix.single_apply] at this
      simp [this]
    · have := key (Pi.single J (Matrix.single m' m' 1)) J l m J l' m'
      simp [Matrix.single_apply, Ne.symm hm] at this
      rw [if_neg hm, mul_zero]
      exact this.symm
  · refine Eq.trans ?_ (blockC_apply_ne _ hJ _ _).symm
    have := key (Pi.single J' (Matrix.single m' m' 1)) J l m J' l' m'
    simp [Matrix.single_apply, Pi.single_eq_of_ne hJ] at this
    exact this.symm

private lemma blockC_mul (Y Z : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    blockC n d Y * blockC n d Z = blockC n d (fun J => Y J * Z J) := by
  simp [blockC, ← Matrix.blockDiagonal'_mul, ← Matrix.mul_kronecker_mul]

private lemma blockC_add (Y Z : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    blockC n d Y + blockC n d Z = blockC n d (fun J => Y J + Z J) := by
  unfold blockC
  rw [← Matrix.blockDiagonal'_add]
  congr 1
  funext J
  exact (Matrix.add_kronecker _ _ _).symm

private lemma blockC_smul (c : ℂ) (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    c • blockC n d Y = blockC n d (fun J => c • Y J) := by
  unfold blockC
  rw [← Matrix.blockDiagonal'_smul]
  congr 1
  funext J
  exact (Matrix.smul_kronecker c (Y J) 1).symm

private lemma exp_kronecker_one {a b : ℕ} (Y : Matrix (Fin a) (Fin a) ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
      NormedSpace.exp Y ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
  let f : Matrix (Fin a) (Fin a) ℂ →+* Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
    { toFun := fun Y => Y ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun A B => by rw [← Matrix.mul_kronecker_mul, one_mul]
      map_zero' := Matrix.zero_kronecker _
      map_add' := fun A B => Matrix.add_kronecker _ _ _ }
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    change Continuous fun Y : Matrix (Fin a) (Fin a) ℂ => Y i.1 j.1 * (1 : Matrix _ _ ℂ) i.2 j.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

private lemma exp_blockC (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    NormedSpace.exp (blockC n d Y) = blockC n d (fun J => NormedSpace.exp (Y J)) := by
  unfold blockC
  rw [Matrix.exp_blockDiagonal']
  congr 1
  funext J
  rw [← exp_kronecker_one]
  have h : NormedSpace.exp (fun J => Y J ⊗ₖ (1 : Matrix (Fin (d J)) (Fin (d J)) ℂ)) =
      fun J => NormedSpace.exp (Y J ⊗ₖ (1 : Matrix (Fin (d J)) (Fin (d J)) ℂ)) := by
    open scoped Matrix.Norms.Operator in
    exact Pi.exp_def _
  exact congrFun h J


private lemma blockC_mul_apply (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (M : Matrix Idx Idx ℂ) (J : 𝒥) (l : Fin (n J)) (m : Fin (d J)) (q : Idx) :
    (blockC n d Y * M) ⟨J, (l, m)⟩ q = ∑ l2, Y J l l2 * M ⟨J, (l2, m)⟩ q := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single m]
    · simp [blockC, Matrix.blockDiagonal'_apply_eq]
    · intro m2 _ hm
      simp [blockC, Matrix.blockDiagonal'_apply_eq, Ne.symm hm]
    · simp
  · intro J2 _ hJ
    simp [blockC, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hJ)]
  · simp

private lemma mul_blockC_apply (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ)
    (M : Matrix Idx Idx ℂ) (p : Idx) (J : 𝒥) (l : Fin (n J)) (m : Fin (d J)) :
    (M * blockC n d Y) p ⟨J, (l, m)⟩ = ∑ l2, M p ⟨J, (l2, m)⟩ * Y J l2 l := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single m]
    · simp [blockC, Matrix.blockDiagonal'_apply_eq]
    · intro m2 _ hm
      simp [blockC, Matrix.blockDiagonal'_apply_eq, hm]
    · simp
  · intro J2 _ hJ
    simp [blockC, Matrix.blockDiagonal'_apply_ne _ _ _ hJ]
  · simp

private lemma blockA_apply_same (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ) (J : 𝒥)
    (l l' : Fin (n J)) (m m' : Fin (d J)) :
    blockA n d X ⟨J, (l, m)⟩ ⟨J, (l', m')⟩ = (if l = l' then 1 else 0) * X J m m' := by
  simp [blockA, Matrix.blockDiagonal'_apply_eq, Matrix.one_apply]

private lemma blockA_apply_ne (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ) {J J' : 𝒥}
    (h : J ≠ J') (x : Fin (n J) × Fin (d J)) (y : Fin (n J') × Fin (d J')) :
    blockA n d X ⟨J, x⟩ ⟨J', y⟩ = 0 := by
  simp [blockA, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- The commutant of `⊕ M_{n_J} ⊗ I` is `⊕ I ⊗ M_{d_J}`. -/
private lemma eq_blockA_of_commute (hn : ∀ J, 0 < n J) (M : Matrix Idx Idx ℂ)
    (hM : ∀ Y, blockC n d Y * M = M * blockC n d Y) :
    M = blockA n d fun J m m' => M ⟨J, (⟨0, hn J⟩, m)⟩ ⟨J, (⟨0, hn J⟩, m')⟩ := by
  have key : ∀ (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) (J : 𝒥) (l : Fin (n J))
      (m : Fin (d J)) (J' : 𝒥) (l' : Fin (n J')) (m' : Fin (d J')),
      ∑ l2, Y J l l2 * M ⟨J, (l2, m)⟩ ⟨J', (l', m')⟩ =
        ∑ l2, M ⟨J, (l, m)⟩ ⟨J', (l2, m')⟩ * Y J' l2 l' := by
    intro Y J l m J' l' m'
    rw [← blockC_mul_apply, ← mul_blockC_apply, hM]
  refine Matrix.ext fun ⟨J, l, m⟩ ⟨J', l', m'⟩ => ?_
  by_cases hJ : J = J'
  · subst hJ
    refine Eq.trans ?_ (blockA_apply_same _ J l l' m m').symm
    by_cases hl : l = l'
    · subst hl
      have := key (Pi.single J (Matrix.single l ⟨0, hn J⟩ 1)) J l m J ⟨0, hn J⟩ m'
      simp [Matrix.single_apply] at this
      simp [this]
    · have := key (Pi.single J (Matrix.single l' l' 1)) J l m J l' m'
      simp [Matrix.single_apply, Ne.symm hl] at this
      rw [if_neg hl, zero_mul]
      exact this.symm
  · refine Eq.trans ?_ (blockA_apply_ne _ hJ _ _).symm
    have := key (Pi.single J' (Matrix.single l' l' 1)) J l m J' l' m'
    simp [Matrix.single_apply, Pi.single_eq_of_ne hJ] at this
    exact this.symm

private lemma blockA_comm_blockC (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ)
    (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    blockA n d X * blockC n d Y = blockC n d Y * blockA n d X := by
  simp [blockA, blockC, ← Matrix.blockDiagonal'_mul, ← Matrix.mul_kronecker_mul]

private lemma blockC_single_one (K : 𝒥) :
    blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K 1) =
      blockA n d (Pi.single (M := fun J => Matrix (Fin (d J)) (Fin (d J)) ℂ) K 1) := by
  unfold blockA blockC
  congr 1
  funext J
  by_cases h : J = K
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]


private lemma conjMul {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix Idx ι ℂ) (hW₂ : W * W.conjTranspose = 1) (A B : Matrix Idx Idx ℂ) :
    (W.conjTranspose * A * W) * (W.conjTranspose * B * W) = W.conjTranspose * (A * B) * W := by
  calc (W.conjTranspose * A * W) * (W.conjTranspose * B * W)
      = W.conjTranspose * A * (W * W.conjTranspose) * B * W := by simp only [Matrix.mul_assoc]
    _ = W.conjTranspose * (A * B) * W := by rw [hW₂]; simp only [Matrix.mul_assoc, Matrix.mul_one]

private lemma conj_uncon {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix Idx ι ℂ) (hW₁ : W.conjTranspose * W = 1) (H : Matrix ι ι ℂ) :
    H = W.conjTranspose * (W * H * W.conjTranspose) * W := by
  calc H = (W.conjTranspose * W) * H * (W.conjTranspose * W) := by
        rw [hW₁, Matrix.one_mul, Matrix.mul_one]
    _ = W.conjTranspose * (W * H * W.conjTranspose) * W := by simp only [Matrix.mul_assoc]

/-- Conjugating by `W` transports commutation. -/
private lemma uncon_comm {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix Idx ι ℂ) (hW₂ : W * W.conjTranspose = 1) (A : Matrix Idx Idx ℂ)
    (H : Matrix ι ι ℂ)
    (h : (W.conjTranspose * A * W) * H = H * (W.conjTranspose * A * W)) :
    A * (W * H * W.conjTranspose) = (W * H * W.conjTranspose) * A := by
  calc A * (W * H * W.conjTranspose)
      = (W * W.conjTranspose) * A * (W * H * W.conjTranspose) := by rw [hW₂, Matrix.one_mul]
    _ = W * ((W.conjTranspose * A * W) * H) * W.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = W * (H * (W.conjTranspose * A * W)) * W.conjTranspose := by rw [h]
    _ = (W * H * W.conjTranspose) * A * (W * W.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = (W * H * W.conjTranspose) * A := by rw [hW₂, Matrix.mul_one]

/-- The commutant of `A` is contained in `{W† blockC Y W}`. -/
private lemma centralizer_sub {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix Idx ι ℂ) (hd : ∀ J, 0 < d J) (hW₁ : W.conjTranspose * W = 1)
    (hW₂ : W * W.conjTranspose = 1) (H : Matrix ι ι ℂ)
    (hH : H ∈ Set.centralizer (algebraA n d W)) :
    H = W.conjTranspose * blockC n d (fun J l l' =>
      (W * H * W.conjTranspose) ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩) * W := by
  rw [Set.mem_centralizer_iff] at hH
  have h := eq_blockC_of_commute hd _
    (fun X => uncon_comm W hW₂ (blockA n d X) H (hH _ ⟨X, rfl⟩))
  rw [← h]
  exact conj_uncon W hW₁ H

private lemma blockC_mem_centralizer {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix Idx ι ℂ) (hW₂ : W * W.conjTranspose = 1)
    (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    W.conjTranspose * blockC n d Y * W ∈ Set.centralizer (algebraA n d W) := by
  rw [Set.mem_centralizer_iff]
  rintro _ ⟨X, rfl⟩
  rw [conjMul W hW₂, conjMul W hW₂, blockA_comm_blockC]

end aux

end BaconThesis.Commutant.Sol_lemma_7_3_1

open BaconThesis.Commutant BaconThesis.Commutant.Sol_lemma_7_3_1

theorem solution {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1)
    (K : 𝒥) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (hHA : H ∈ Set.centralizer (algebraA n d W)) :
    H * irrepProj n d W K = irrepProj n d W K * H ∧
      ∃ Y : Matrix (Fin (n K)) (Fin (n K)) ℂ, Y.IsHermitian ∧
        H * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K Y) * W ∧
        ∀ t : ℝ, NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K
              (NormedSpace.exp ((-(t : ℂ) * Complex.I) • Y))) * W := by
  have conj_mul := conjMul W hW₂
  have exp_conj : ∀ A : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ,
      NormedSpace.exp (W.conjTranspose * A * W) = W.conjTranspose * NormedSpace.exp A * W := by
    intro A
    let f : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ →+*
        Matrix ι ι ℂ :=
      { toFun := fun A => W.conjTranspose * A * W
        map_one' := by rw [Matrix.mul_one, hW₁]
        map_mul' := fun A B => (conj_mul A B).symm
        map_zero' := by simp
        map_add' := fun A B => by rw [Matrix.mul_add, Matrix.add_mul] }
    have hf : Continuous f := by
      change Continuous fun A : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J))
        (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ => W.conjTranspose * A * W
      fun_prop
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp f hf A).symm
  have struct := centralizer_sub W hd hW₁ hW₂ H hHA
  set Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ := fun J l l' =>
    (W * H * W.conjTranspose) ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩ with hY
  have hHY : H = W.conjTranspose * blockC n d Y * W := struct
  have hHP : H * irrepProj n d W K = W.conjTranspose * blockC n d (Pi.single K (Y K)) * W := by
    rw [irrepProj]
    nth_rewrite 1 [hHY]
    rw [conj_mul, blockC_mul]
    congr 3
    funext J
    by_cases h : J = K
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hPH : irrepProj n d W K * H = W.conjTranspose * blockC n d (Pi.single K (Y K)) * W := by
    rw [irrepProj]
    nth_rewrite 1 [hHY]
    rw [conj_mul, blockC_mul]
    congr 3
    funext J
    by_cases h : J = K
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  refine ⟨hHP.trans hPH.symm, Y K, ?_, hHP, fun t => ?_⟩
  · have hherm : (W * H * W.conjTranspose).IsHermitian := by
      have := hH
      unfold Matrix.IsHermitian at this ⊢
      simp [Matrix.conjTranspose_mul, this, Matrix.mul_assoc]
    ext l l'
    rw [Matrix.conjTranspose_apply]
    exact hherm.apply ⟨K, (l, ⟨0, hd K⟩)⟩ ⟨K, (l', ⟨0, hd K⟩)⟩
  · set c : ℂ := -(t : ℂ) * Complex.I
    have hexp : NormedSpace.exp (c • H) =
        W.conjTranspose * blockC n d (fun J => NormedSpace.exp (c • Y J)) * W := by
      have h1 : c • H = W.conjTranspose * blockC n d (fun J => c • Y J) * W := by
        rw [← blockC_smul]
        nth_rewrite 1 [hHY]
        simp only [Matrix.mul_smul, Matrix.smul_mul]
      rw [h1, exp_conj, exp_blockC]
    rw [irrepProj, hexp, conj_mul, blockC_mul]
    congr 3
    funext J
    by_cases h : J = K
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
