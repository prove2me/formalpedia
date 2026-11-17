-- Prove2me | solution 1 for BaconThesis.Commutant.lemma_7_3_2
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T10:13:44.653199+00:00
-- url     : https://prove2.me/submissions/6ce736c6-1cd3-4e1c-bc11-5a859e9293f5

import Mathlib
import Definitions.Def_BaconThesis_Commutant_algebraA
import Definitions.Def_BaconThesis_Commutant_blockA
import Definitions.Def_BaconThesis_Commutant_blockC
import Definitions.Def_BaconThesis_Commutant_irrepProj
import Definitions.Def_BaconThesis_Commutant_lieGen

open scoped Kronecker
attribute [local instance 100] LieRing.ofAssociativeRing

namespace BaconThesis.Commutant.Sol732

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

end aux

end BaconThesis.Commutant.Sol732

open BaconThesis.Commutant BaconThesis.Commutant.Sol732

theorem solution {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1)
    (K : 𝒥) (S : Set (Matrix ι ι ℂ))
    (hS : ∀ H ∈ S, H.IsHermitian ∧ H ∈ Set.centralizer (algebraA n d W)) :
    (∀ H ∈ S, H * irrepProj n d W K = irrepProj n d W K * H ∧
      ∃ Y : Matrix (Fin (n K)) (Fin (n K)) ℂ, Y.IsHermitian ∧
        H * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K Y) * W ∧
        ∀ t : ℝ, NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K
              (NormedSpace.exp ((-(t : ℂ) * Complex.I) • Y))) * W) ∧
    ∀ X ∈ lieGen S, ∃ Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ,
      X = W.conjTranspose * blockC n d Y * W := by
  -- conjugation calculus
  have conj_mul : ∀ A B : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ,
      (W.conjTranspose * A * W) * (W.conjTranspose * B * W) = W.conjTranspose * (A * B) * W := by
    intro A B
    calc (W.conjTranspose * A * W) * (W.conjTranspose * B * W)
        = W.conjTranspose * A * (W * W.conjTranspose) * B * W := by simp only [Matrix.mul_assoc]
      _ = W.conjTranspose * (A * B) * W := by rw [hW₂]; simp only [Matrix.mul_assoc, Matrix.mul_one]
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
  -- every commuting Hamiltonian is `W† blockC Y W`, with `Y` read off its matrix elements
  have struct : ∀ H ∈ S, H = W.conjTranspose * blockC n d (fun J l l' =>
      (W * H * W.conjTranspose) ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩) * W := by
    intro H hH
    have hc := (hS H hH).2
    rw [Set.mem_centralizer_iff] at hc
    have hM : ∀ X, blockA n d X * (W * H * W.conjTranspose) =
        (W * H * W.conjTranspose) * blockA n d X := by
      intro X
      have h := hc (W.conjTranspose * blockA n d X * W) ⟨X, rfl⟩
      calc blockA n d X * (W * H * W.conjTranspose)
          = (W * W.conjTranspose) * blockA n d X * (W * H * W.conjTranspose) := by
            rw [hW₂, Matrix.one_mul]
        _ = W * ((W.conjTranspose * blockA n d X * W) * H) * W.conjTranspose := by
            simp only [Matrix.mul_assoc]
        _ = W * (H * (W.conjTranspose * blockA n d X * W)) * W.conjTranspose := by rw [h]
        _ = (W * H * W.conjTranspose) * blockA n d X * (W * W.conjTranspose) := by
            simp only [Matrix.mul_assoc]
        _ = (W * H * W.conjTranspose) * blockA n d X := by rw [hW₂, Matrix.mul_one]
    have h := eq_blockC_of_commute hd _ hM
    calc H = (W.conjTranspose * W) * H * (W.conjTranspose * W) := by
          rw [hW₁, Matrix.one_mul, Matrix.mul_one]
      _ = W.conjTranspose * (W * H * W.conjTranspose) * W := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← h]
  refine ⟨fun H hH => ?_, ?_⟩
  · set Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ := fun J l l' =>
      (W * H * W.conjTranspose) ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩ with hY
    have hHY : H = W.conjTranspose * blockC n d Y * W := struct H hH
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
        have := (hS H hH).1
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
  · let L : LieSubalgebra ℝ (Matrix ι ι ℂ) :=
      { carrier := {X | ∃ Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ,
          X = W.conjTranspose * blockC n d Y * W}
        add_mem' := by
          rintro _ _ ⟨Y, rfl⟩ ⟨Z, rfl⟩
          exact ⟨fun J => Y J + Z J, by rw [← blockC_add, Matrix.mul_add, Matrix.add_mul]⟩
        zero_mem' := ⟨fun J => (0 : ℂ) • 0, by rw [← blockC_smul]; simp⟩
        smul_mem' := by
          rintro r _ ⟨Y, rfl⟩
          refine ⟨fun J => (r : ℂ) • Y J, ?_⟩
          rw [← blockC_smul, ← Complex.coe_smul]
          simp only [Matrix.mul_smul, Matrix.smul_mul]
        lie_mem' := by
          rintro _ _ ⟨Y, rfl⟩ ⟨Z, rfl⟩
          refine ⟨fun J => Y J * Z J + (-1 : ℂ) • (Z J * Y J), ?_⟩
          rw [Ring.lie_def, conj_mul, conj_mul, blockC_mul, blockC_mul, ← blockC_add,
            ← blockC_smul]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
          simp [sub_eq_add_neg] }
    have hle : lieGen S ≤ L := by
      rw [lieGen, LieSubalgebra.lieSpan_le]
      rintro _ ⟨H, hH, rfl⟩
      let Y0 : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ := fun J l l' =>
        (W * H * W.conjTranspose) ⟨J, (l, ⟨0, hd J⟩)⟩ ⟨J, (l', ⟨0, hd J⟩)⟩
      have h : H = W.conjTranspose * blockC n d Y0 * W := struct H hH
      refine ⟨fun J => Complex.I • Y0 J, ?_⟩
      change Complex.I • H = _
      rw [← blockC_smul Complex.I Y0]
      nth_rewrite 1 [h]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    exact fun X hX => hle hX
