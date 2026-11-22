-- Prove2me | solution 1 for GL2QFT.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:15:01.033589+00:00
-- url     : https://prove2.me/submissions/d4d9f7a3-2e18-47c4-9ad7-8870803a992c

import Definitions.Def_GL2QFT_InductionTransform

open Classical GL2QFT Induction

theorem solution {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (T : Set G)
    [Fintype T] (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsMatRep (RG μ)) (hAd : IsSubgroupAdapted H BH Nminus RH RG) :
    Function.Bijective (ident BH Nminus) ∧
    fourierMatrix RG =
      ((UIndTensorI T BH Nminus RG * Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)) *
        Enc H T).submatrix (ident BH Nminus) id := by
  constructor
  · refine Function.bijective_iff_has_inverse.mpr
      ⟨fun x => ⟨x.2.1.1.1, x.2.1.2, ⟨⟨x.1, x.2.1.1.2⟩, x.2.2⟩⟩,
        fun _ => rfl, fun _ => rfl⟩
  · ext o g
    rcases o with ⟨μ, Q, ⟨⟨l, hl⟩, R⟩⟩
    obtain ⟨⟨t₀, ⟨h₀, hh₀⟩⟩, hth₀, huniq⟩ := hT.existsUnique g
    let h₀H : H := ⟨h₀, hh₀⟩
    have hth₀' : (t₀ : G) * (h₀H : G) = g := hth₀
    have hEnc : ∀ th : T × H, Enc H T th g = if th = (t₀, h₀H) then 1 else 0 := by
      intro th
      have hiff : g = (th.1 : G) * (th.2 : G) ↔ th = (t₀, h₀H) := by
        constructor
        · intro h
          have hpair : (th.1, (⟨th.2.1, th.2.2⟩ : (H : Set G))) = (t₀, ⟨h₀, hh₀⟩) :=
            huniq (th.1, ⟨th.2.1, th.2.2⟩) h.symm
          exact Prod.ext (congrArg Prod.fst hpair) (Subtype.ext (congrArg (fun p => p.2.1) hpair))
        · rintro rfl
          exact hth₀'.symm
      simp only [Enc, Matrix.of_apply, hiff]
    simp only [Matrix.submatrix_apply, id_eq]
    rw [Matrix.mul_apply]
    have hsum1 :
        ∑ th : T × H,
          (UIndTensorI T BH Nminus RG *
            Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH))
            (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) th * Enc H T th g =
          (UIndTensorI T BH Nminus RG *
            Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH))
            (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t₀, h₀H) := by
      refine (Finset.sum_eq_single (t₀, h₀H) ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
      · intro th _ hne
        rw [hEnc th, if_neg hne, mul_zero]
      · rw [hEnc (t₀, h₀H), if_pos rfl, mul_one]
    rw [hsum1, Matrix.mul_apply, Fintype.sum_prod_type]
    have hsum_t :
        ∑ t' : T, ∑ x : (Σ l' : ΛH, BH l' × BH l'),
          UIndTensorI T BH Nminus RG (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t', x) *
            Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH) (t', x) (t₀, h₀H) =
          ∑ x : (Σ l' : ΛH, BH l' × BH l'),
            UIndTensorI T BH Nminus RG (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t₀, x) *
              fourierMatrix RH x h₀H := by
      refine (Finset.sum_eq_single t₀ ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
      · intro t' _ hne
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_ne hne, zero_mul, mul_zero]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul]
    rw [hsum_t, Fintype.sum_sigma]
    have hsum_l :
        ∑ l' : ΛH, ∑ pr : BH l' × BH l',
          UIndTensorI T BH Nminus RG (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t₀, ⟨l', pr⟩) *
            fourierMatrix RH ⟨l', pr⟩ h₀H =
          ∑ pr : BH l × BH l,
            UIndTensorI T BH Nminus RG (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t₀, ⟨l, pr⟩) *
              fourierMatrix RH ⟨l, pr⟩ h₀H := by
      refine Finset.sum_eq_single l ?_ fun hmem => absurd (Finset.mem_univ _) hmem
      intro l' _ hne
      refine Finset.sum_eq_zero fun pr _ => ?_
      simp only [UIndTensorI, Matrix.of_apply, ident, dif_neg hne, zero_mul]
    rw [hsum_l, Fintype.sum_prod_type]
    have hsum_R :
        ∑ P' : BH l, ∑ R' : BH l,
          UIndTensorI T BH Nminus RG (ident BH Nminus ⟨μ, (Q, ⟨⟨l, hl⟩, R⟩)⟩) (t₀, ⟨l, (P', R')⟩) *
            fourierMatrix RH ⟨l, (P', R')⟩ h₀H =
          ∑ P' : BH l,
            UIndLam T BH Nminus RG l ⟨⟨μ, hl⟩, Q⟩ (t₀, P') *
              fourierMatrix RH ⟨l, (P', R)⟩ h₀H := by
      refine Finset.sum_congr rfl fun P' _ => ?_
      refine (Finset.sum_eq_single R ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
      · intro R' _ hne
        simp [UIndTensorI, ident, hne]
      · simp [UIndTensorI, ident]
    rw [hsum_R]
    simp only [fourierMatrix, Matrix.of_apply]
    have hg : g = (t₀ : G) * (h₀H : G) := hth₀'.symm
    rw [hg, (hRG μ).2 (t₀ : G) (h₀H : G), Matrix.mul_apply, Fintype.sum_sigma]
    have hsum_lhs :
        ∑ l' : Nminus μ, ∑ P' : BH l'.1,
          RG μ (t₀ : G) Q ⟨l', P'⟩ * RG μ (h₀H : G) ⟨l', P'⟩ ⟨⟨l, hl⟩, R⟩ =
          ∑ P' : BH l, RG μ (t₀ : G) Q ⟨⟨l, hl⟩, P'⟩ * RH l h₀H P' R := by
      refine (Finset.sum_eq_single ⟨l, hl⟩ ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
      · intro l' _ hne
        refine Finset.sum_eq_zero fun P' _ => ?_
        rw [hAd μ h₀H ⟨l', P'⟩ ⟨⟨l, hl⟩, R⟩]
        dsimp only
        rw [dif_neg hne, mul_zero]
      · refine Finset.sum_congr rfl fun P' _ => ?_
        rw [hAd μ h₀H ⟨⟨l, hl⟩, P'⟩ ⟨⟨l, hl⟩, R⟩]
        dsimp only
        rw [dif_pos rfl, cast_eq]
    rw [hsum_lhs]
    simp only [UIndLam, Matrix.of_apply]
    have hfactor :
        ∑ P' : BH l,
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
            RG μ (t₀ : G) Q ⟨⟨l, hl⟩, P'⟩) *
          ((Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H : ℝ)) : ℂ) *
            RH l h₀H P' R) =
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
            (Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H : ℝ)) : ℂ)) *
          ∑ P' : BH l, RG μ (t₀ : G) Q ⟨⟨l, hl⟩, P'⟩ * RH l h₀H P' R := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P' _ => ?_
      ring
    rw [hfactor]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    have hcard_mul : Fintype.card T * Fintype.card H = Fintype.card G := by
      simpa only [← Fintype.card_prod] using
        Fintype.card_congr (Equiv.ofBijective (fun x : T × H => (x.1 : G) * (x.2 : G)) hT)
    have hBH_pos : 0 < Fintype.card (BH l) := Fintype.card_pos_iff.mpr ⟨R⟩
    have hG_pos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨g⟩
    have hT_ne : (Fintype.card T : ℝ) ≠ 0 := by
      intro h0
      have : Fintype.card T = 0 := Nat.cast_eq_zero.mp h0
      rw [this, zero_mul] at hcard_mul
      omega
    have hH_ne : (Fintype.card H : ℝ) ≠ 0 := by
      intro h0
      have : Fintype.card H = 0 := Nat.cast_eq_zero.mp h0
      rw [this, mul_zero] at hcard_mul
      omega
    have hBH_ne : (Fintype.card (BH l) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hBH_pos.ne'
    have hcard_R : (Fintype.card G : ℝ) = (Fintype.card T : ℝ) * (Fintype.card H : ℝ) := by
      exact_mod_cast hcard_mul.symm
    rw [hcard_R]
    field_simp
