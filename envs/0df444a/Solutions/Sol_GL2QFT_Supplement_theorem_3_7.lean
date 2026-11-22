-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:26:32.97383+00:00
-- url     : https://prove2.me/submissions/6d3786fc-854b-4341-85bf-b1e1677594c5

import Definitions.Def_GL2QFT_Supplement_Chain

noncomputable section

open Classical

section
open GL2QFT GL2QFT.Induction GL2QFT.Supplement GL2QFT.Supplement.Chain

private lemma lemma_3_5_matrix {G' : Type} [Group G'] [Fintype G']
    (H' : Subgroup G') [Fintype H'] (T' : Set G') [Fintype T'] [DecidableEq T']
    (hT : Subgroup.IsComplement T' (H' : Set G'))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG]
    (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H' → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G' → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (instFRG : ∀ μ, Fintype (AdBas BH Nminus μ))
    (instDRG : ∀ μ, DecidableEq (AdBas BH Nminus μ))
    (hRG : ∀ μ, @IsMatRep G' (AdBas BH Nminus μ) _ (instFRG μ) (instDRG μ) (RG μ))
    (hAd : IsSubgroupAdapted H' BH Nminus RH RG) :
    @fourierMatrix G' ΛG _ (AdBas BH Nminus) instFRG RG =
      ((UIndTensorI T' BH Nminus RG *
          Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH)) *
        Enc H' T').submatrix (ident BH Nminus) id := by
  obtain rfl : instFRG = fun μ => Sigma.instFintype := funext fun μ => Subsingleton.elim _ _
  ext o g
  rcases o with ⟨μ, Q, ⟨l, hl⟩, r⟩
  obtain ⟨⟨t₀, h₀⟩, hmul, huniq⟩ := hT.existsUnique g
  let h₀' : H' := ⟨h₀.1, h₀.2⟩
  have hmul' : (t₀ : G') * (h₀' : G') = g := hmul
  have hKE : ∀ (t : T') (ridx : Σ l' : ΛH, BH l' × BH l'),
      (Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH) * Enc H' T') (t, ridx) g =
        if t = t₀ then fourierMatrix RH ridx h₀' else 0 := by
    intro t ridx
    rw [Matrix.mul_apply, Fintype.sum_eq_single (t₀, h₀')]
    · change (1 : Matrix T' T' ℂ) t t₀ * fourierMatrix RH ridx h₀' * Enc H' T' (t₀, h₀') g = _
      simp only [Enc, Matrix.of_apply, hmul', ↓reduceIte, mul_one, Matrix.one_apply]
      split_ifs <;> simp
    · intro x hx
      have hne : g ≠ (x.1 : G') * (x.2 : G') := by
        intro heq
        apply hx
        have hu := huniq ⟨x.1, ⟨x.2.1, x.2.2⟩⟩ heq.symm
        ext
        · exact congrArg (fun p => (p.1 : G')) hu
        · exact congrArg (fun p => (p.2 : G')) hu
      simp [Enc, hne]
  simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_assoc]
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_eq_single t₀]
  · simp only [hKE, ↓reduceIte]
    rw [Fintype.sum_sigma, Fintype.sum_eq_single l]
    · simp only [UIndTensorI, ident, Matrix.of_apply, ↓reduceDIte, cast_eq]
      rw [Fintype.sum_prod_type_right, Fintype.sum_eq_single r]
      · simp only [↓reduceIte, mul_one]
        have hLHS : fourierMatrix RG ⟨μ, Q, ⟨l, hl⟩, r⟩ g =
            (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) *
              ∑ P : BH l, RG μ (t₀ : G') Q ⟨⟨l, hl⟩, P⟩ * RH l h₀' P r := by
          simp only [fourierMatrix, Matrix.of_apply]
          congr 1
          rw [← hmul', (hRG μ).2, Matrix.mul_apply, Fintype.sum_sigma,
            Fintype.sum_eq_single ⟨l, hl⟩]
          · refine Finset.sum_congr rfl fun P _ => ?_
            rw [hAd μ h₀' ⟨⟨l, hl⟩, P⟩ ⟨⟨l, hl⟩, r⟩]
            simp
          · intro x hx
            refine Finset.sum_eq_zero fun P _ => ?_
            rw [hAd μ h₀' ⟨x, P⟩ ⟨⟨l, hl⟩, r⟩]
            simp [hx]
        rw [hLHS]
        have hcard_mul : Fintype.card T' * Fintype.card H' = Fintype.card G' := by
          have hc := hT.card_mul_card
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
          exact hc
        have hBH_pos : (0 : ℝ) < Fintype.card (BH l) :=
          Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨r⟩)
        have hT_pos : (0 : ℝ) < Fintype.card T' :=
          Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨t₀⟩)
        have hH_pos : (0 : ℝ) < Fintype.card H' :=
          Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨h₀'⟩)
        have hsqrt :
            (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
              (Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ) =
              (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
                (Fintype.card G' : ℝ)) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
          congr 2
          have hG_eq : (Fintype.card G' : ℝ) = (Fintype.card T' : ℝ) * (Fintype.card H' : ℝ) := by
            exact_mod_cast hcard_mul.symm
          rw [hG_eq]
          field_simp
        rw [Finset.mul_sum]
        symm
        refine Finset.sum_congr rfl fun P _ => ?_
        simp only [UIndLam, fourierMatrix, Matrix.of_apply]
        calc
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
              RG μ (t₀ : G') Q ⟨⟨l, hl⟩, P⟩) *
              ((Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ) *
                RH l h₀' P r)
              = ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
                  ((Fintype.card (BH l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
                  (Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ)) *
                  (RG μ (t₀ : G') Q ⟨⟨l, hl⟩, P⟩ * RH l h₀' P r) := by ring
          _ = (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) *
                (RG μ (t₀ : G') Q ⟨⟨l, hl⟩, P⟩ * RH l h₀' P r) := by rw [hsqrt]
      · intro r' hr'
        refine Finset.sum_eq_zero fun P _ => ?_
        simp [hr']
    · intro l' hl'
      refine Finset.sum_eq_zero fun pr _ => ?_
      simp [UIndTensorI, ident, hl']
  · intro t ht
    refine Finset.sum_eq_zero fun ridx _ => ?_
    rw [hKE t ridx, if_neg ht, mul_zero]

theorem solution {G : Type} [Group G] [Fintype G] (N : ℕ) (grp : ℕ → Subgroup G)
    (h0 : grp 0 = ⊥) (hN : grp N = ⊤) (hchain : ∀ k < N, grp k < grp (k + 1))
    (Λ : ℕ → Type) [∀ k, Fintype (Λ k)] (Nm : ∀ k, Λ (k + 1) → Finset (Λ k))
    (R : ∀ k (μ : Λ k), grp k → Matrix (Paths Λ Nm k μ) (Paths Λ Nm k μ) ℂ)
    (hR : ∀ k ≤ N, ∀ μ, IsMatRep (R k μ))
    (hAd : ∀ k < N, IsSubgroupAdapted (lowerSub grp k) (Paths Λ Nm k) (Nm k)
      (fun l h => R k l (toLower grp k h)) (R (k + 1)))
    (T : ∀ k, Set (grp (k + 1)))
    (hT : ∀ k < N, Subgroup.IsComplement (T k) (lowerSub grp k : Set (grp (k + 1)))) :
    chainQ grp Λ Nm R T N = fourierMatrix (R N) := by
  let _ := h0
  let _ := hN
  have hmain : ∀ k ≤ N, chainQ grp Λ Nm R T k = fourierMatrix (R k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < N := by omega
      have ih' : chainQ grp Λ Nm R T k = fourierMatrix (R k) := ih (by omega)
      simp only [chainQ, ih']
      have hsub :
          (fourierMatrix (R k)).submatrix id (toLower grp k) =
            fourierMatrix (fun l (h : lowerSub grp k) => R k l (toLower grp k h)) := by
        ext r h
        simp only [Matrix.submatrix_apply, id_eq, fourierMatrix, Matrix.of_apply]
        have hcard : Fintype.card (lowerSub grp k) = Fintype.card (grp k) := by
          refine Fintype.card_congr ?_
          exact
            { toFun := toLower grp k
              invFun := fun y => ⟨⟨y.1, (le_of_lt (hchain k hk_lt)) y.2⟩, y.2⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [hcard]
      rw [hsub]
      exact (lemma_3_5_matrix (lowerSub grp k) (T k) (hT k hk_lt) (Paths Λ Nm k) (Nm k)
        (fun l h => R k l (toLower grp k h)) (R (k + 1))
        (fun μ => instFintypePaths Λ Nm (k + 1) μ)
        (fun μ => instDecEqPaths Λ Nm (k + 1) μ)
        (hR (k + 1) hk) (hAd k hk_lt)).symm
  exact hmain N (le_refl N)

end
