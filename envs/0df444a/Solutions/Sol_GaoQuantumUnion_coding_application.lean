-- Prove2me | solution 1 for GaoQuantumUnion.coding_application
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:08:54.181522+00:00
-- url     : https://prove2.me/submissions/714e19cb-a16a-4336-8243-2578ca947ed4

import Definitions.Def_GaoQuantumUnion_Decoding
import Theorems.Thm_GaoQuantumUnion_decoder_bound
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GaoCode

variable {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

lemma prod_form {M : ℕ} (f : Fin M → J → ℝ) :
    ∑ C : Fin M → J, ∏ k, f k (C k) = ∏ k, ∑ j, f k j := by
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) f, Fintype.piFinset_univ]

lemma weight_mul_prod {M : ℕ} (p : FinDist J) (φ : Fin M → J → ℝ) :
    ∑ C : Fin M → J, codeWeight p C * ∏ k, φ k (C k) = ∏ k, ∑ j, p.prob j * φ k j := by
  rw [← prod_form]
  refine Finset.sum_congr rfl fun C _ => ?_
  unfold codeWeight
  rw [Finset.prod_mul_distrib]

lemma weight_sum {M : ℕ} (p : FinDist J) : ∑ C : Fin M → J, codeWeight p C = 1 := by
  have := weight_mul_prod (M := M) p (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this, p.sum_eq_one, Finset.prod_const_one]

lemma weight_nonneg {M : ℕ} (p : FinDist J) (C : Fin M → J) : 0 ≤ codeWeight p C :=
  Finset.prod_nonneg fun k _ => p.nonneg _

lemma marg1 {M : ℕ} (p : FinDist J) (m : Fin M) (f : J → ℝ) :
    ∑ C : Fin M → J, codeWeight p C * f (C m) = ∑ x, p.prob x * f x := by
  have := weight_mul_prod p (fun k j => if k = m then f j else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at this
  rw [this]
  rw [Finset.prod_eq_single m]
  · simp
  · intro k _ hk; simp [hk, p.sum_eq_one]
  · simp

lemma marg2 {M : ℕ} (p : FinDist J) (i m : Fin M) (him : i ≠ m) (g : J → J → ℝ) :
    ∑ C : Fin M → J, codeWeight p C * g (C i) (C m) =
      ∑ x, ∑ y, p.prob x * p.prob y * g x y := by
  have key : ∀ a b : J, ∑ C : Fin M → J, codeWeight p C *
      ((if C i = a then 1 else 0) * (if C m = b then 1 else 0)) = p.prob a * p.prob b := by
    intro a b
    have := weight_mul_prod p (fun k j => (if k = i then (if j = a then (1:ℝ) else 0) else 1) *
      (if k = m then (if j = b then (1:ℝ) else 0) else 1))
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true] at this
    rw [this]
    have hk : ∀ k : Fin M, ∑ j, p.prob j * ((if k = i then (if j = a then (1:ℝ) else 0) else 1) *
        (if k = m then (if j = b then (1:ℝ) else 0) else 1)) =
        (if k = i then p.prob a else 1) * (if k = m then p.prob b else 1) := by
      intro k
      by_cases h1 : k = i
      · have h2 : k ≠ m := h1 ▸ him
        simp [h1, him]
      · by_cases h2 : k = m
        · simp [h2, Ne.symm him]
        · simp [h1, h2, p.sum_eq_one]
    simp only [hk, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hg : ∀ C : Fin M → J, g (C i) (C m) = ∑ a, ∑ b, g a b *
      ((if C i = a then 1 else 0) * (if C m = b then 1 else 0)) := by
    intro C
    simp [mul_ite, ite_mul, Finset.sum_ite_eq]
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← key a b, Finset.sum_mul]
  refine Finset.sum_congr rfl fun C _ => ?_
  ring


lemma avg_algebra {M : ℕ} (p : FinDist J) (m : Fin M) (F : Finset (Fin M))
    (hF : ∀ i ∈ F, i ≠ m) (a b : J → ℝ) (c : J → J → ℝ) :
    ∑ C : Fin M → J, codeWeight p C * (a (C m) - 4 * b (C m) - 4 * ∑ i ∈ F, c (C i) (C m)) =
      ∑ x, p.prob x * a x - 4 * ∑ x, p.prob x * b x
        - 4 * ∑ i ∈ F, ∑ x, ∑ y, p.prob x * p.prob y * c x y := by
  have e : ∀ C : Fin M → J, codeWeight p C * (a (C m) - 4 * b (C m) - 4 * ∑ i ∈ F, c (C i) (C m))
      = codeWeight p C * a (C m) - 4 * (codeWeight p C * b (C m))
        - 4 * ∑ i ∈ F, codeWeight p C * c (C i) (C m) := by
    intro C; rw [← Finset.mul_sum]; ring
  rw [Finset.sum_congr rfl fun C _ => e C, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm, marg1, marg1]
  congr 2
  exact Finset.sum_congr rfl fun i hi => marg2 p i m (hF i hi) c

section matrices
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma trace_mul_psd_nonneg (X ρ : Matrix ι ι ℂ) (hX : X.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ (X * ρ).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [star_eq_conjTranspose, mul_assoc, trace_mul_comm]
  have := (hρ.mul_mul_conjTranspose_same C).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma proj_psd {X : Matrix ι ι ℂ} (h : IsProjector X) : X.PosSemidef := by
  have := posSemidef_conjTranspose_mul_self X
  rwa [h.1.eq, h.2] at this

lemma one_sub_proj {X : Matrix ι ι ℂ} (h : IsProjector X) : IsProjector (1 - X) := by
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [conjTranspose_sub, conjTranspose_one, h.1.eq]
  · rw [show (1 - X) * (1 - X) = 1 - X - X + X * X by noncomm_ring, h.2]; abel

lemma alg1 (R P' : Matrix ι ι ℂ) :
    (1 + P') * R * (1 + P') = R + R + (P' * R * P' + P' * R * P') - (1 - P') * R * (1 - P') := by
  noncomm_ring

lemma gentle_core (P' Q ρ : Matrix ι ι ℂ) (hP'h : P'ᴴ = P') (hP'2 : P' * P' = P')
    (hQ : IsProjector Q) (hρ : ρ.PosSemidef) :
    ((1 - P') * (1 - Q) * (1 - P') * ρ).trace.re ≤
      2 * ((1 - Q) * ρ).trace.re + 2 * (P' * ρ).trace.re := by
  have hR : (1 - Q).PosSemidef := proj_psd (one_sub_proj hQ)
  have h1 := trace_mul_psd_nonneg _ ρ (hR.conjTranspose_mul_mul_same (1 + P')) hρ
  rw [conjTranspose_add, conjTranspose_one, hP'h, alg1] at h1
  have h2 := trace_mul_psd_nonneg _ ρ ((proj_psd hQ).conjTranspose_mul_mul_same P') hρ
  have e2 : P'ᴴ * Q * P' = P' - P' * (1 - Q) * P' := by
    rw [hP'h, show P' * Q * P' = P' * P' - P' * (1 - Q) * P' by noncomm_ring, hP'2]
  rw [e2] at h2
  generalize (1 - P') * (1 - Q) * (1 - P') = T at h1 ⊢
  generalize P' * (1 - Q) * P' = S at h1 h2
  generalize 1 - Q = R at h1 h2 ⊢
  simp only [sub_mul, add_mul, trace_sub, trace_add, Complex.sub_re, Complex.add_re] at h1 h2
  linarith

lemma gentle (P Q ρ : Matrix ι ι ℂ) (hP : IsProjector P) (hQ : IsProjector Q)
    (hρ : ρ.PosSemidef) :
    (P * (1 - Q) * P * ρ).trace.re ≤
      2 * ((1 - Q) * ρ).trace.re + 2 * ((1 - P) * ρ).trace.re := by
  have := gentle_core (1 - P) Q ρ (one_sub_proj hP).1.eq (one_sub_proj hP).2 hQ hρ
  rwa [sub_sub_cancel] at this

lemma per_term {M : ℕ} (P : Matrix ι ι ℂ) (hP : IsProjector P) (Q' : Fin M → Matrix ι ι ℂ)
    (hQ' : ∀ i, IsProjector (Q' i)) (m : Fin M) (σ : Matrix ι ι ℂ) (hσ : σ.PosSemidef) :
    (P * σ).trace.re - 4 * (P * (1 - Q' m) * P * σ).trace.re -
      4 * ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val < m.val), (P * Q' i * P * σ).trace.re
      ≤ (decoderK P Q' m * σ * (decoderK P Q' m)ᴴ).trace.re := by
  have h := trace_mul_psd_nonneg _ σ (decoder_bound P hP Q' hQ' m) hσ
  rw [trace_mul_cycle (decoderK P Q' m) σ (decoderK P Q' m)ᴴ]
  unfold decoderEffect at h
  simp only [sub_mul, smul_mul_assoc, Finset.sum_mul, trace_sub, trace_smul, trace_sum,
    Complex.sub_re, Complex.re_sum, smul_eq_mul, Complex.mul_re] at h
  norm_num at h ⊢
  linarith

end matrices

end GaoCode

open GaoCode in
theorem solution {ι J : Type} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] (p : FinDist J) (ρ : J → Matrix ι ι ℂ)
    (hρ : ∀ j, IsDensityOperator (ρ j)) (P : Matrix ι ι ℂ) (hP : IsProjector P)
    (Q : J → Matrix ι ι ℂ) (hQ : ∀ j, IsProjector (Q j))
    (ε A B : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (havg : 1-ε ≤ (P*WildeQIT.Gentle.averageState p ρ).trace.re)
    (hdetect : ∀ j, 1-ε ≤ (Q j*ρ j).trace.re)
    (hsize : ∀ j, (Q j).trace.re ≤ B)
    (hsandwich : ((A : ℂ) • (1 : Matrix ι ι ℂ)-P*WildeQIT.Gentle.averageState p ρ*P).PosSemidef)
    (M : ℕ) (hM : 0 < M) :
    (∑ C : Fin M → J, codeWeight p C*codeError ρ P Q C) ≤ 33*ε+4*((M : ℝ)-1)*A*B ∧
    ∃ C : Fin M → J, codeError ρ P Q C ≤ 33*ε+4*((M : ℝ)-1)*A*B := by
  set ρbar := WildeQIT.Gentle.averageState p ρ with hρbar
  -- linear functional averaging
  have avg_lin : ∀ X : Matrix ι ι ℂ,
      ∑ x, p.prob x * (X * ρ x).trace.re = (X * ρbar).trace.re := by
    intro X
    simp [hρbar, WildeQIT.Gentle.averageState, Matrix.mul_sum, trace_sum, Complex.re_sum,
      mul_smul_comm, trace_smul]
  have one_sub : ∀ x, ((1 - P) * ρ x).trace.re = 1 - (P * ρ x).trace.re := by
    intro x
    rw [sub_mul, one_mul, trace_sub, (hρ x).2, Complex.sub_re, Complex.one_re]
  -- per-letter bound for b
  have hb : ∀ x, (P * (1 - Q x) * P * ρ x).trace.re ≤ 2 * ε + 2 * (1 - (P * ρ x).trace.re) := by
    intro x
    have g := gentle P (Q x) (ρ x) hP (hQ x) (hρ x).1
    have hq : ((1 - Q x) * ρ x).trace.re = 1 - (Q x * ρ x).trace.re := by
      rw [sub_mul, one_mul, trace_sub, (hρ x).2, Complex.sub_re, Complex.one_re]
    rw [hq, one_sub] at g
    linarith [hdetect x]
  have abar : 1 - ε ≤ ∑ x, p.prob x * (P * ρ x).trace.re := by rw [avg_lin]; exact havg
  have bbar : ∑ x, p.prob x * (P * (1 - Q x) * P * ρ x).trace.re ≤ 4 * ε := by
    calc ∑ x, p.prob x * (P * (1 - Q x) * P * ρ x).trace.re
        ≤ ∑ x, p.prob x * (2 * ε + 2 * (1 - (P * ρ x).trace.re)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x) (p.nonneg x)
      _ = 2 * ε * ∑ x, p.prob x + 2 * ∑ x, p.prob x - 2 * ∑ x, p.prob x * (P * ρ x).trace.re := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ 4 * ε := by rw [p.sum_eq_one]; linarith
  have cbar : ∑ x, ∑ y, p.prob x * p.prob y * (P * Q x * P * ρ y).trace.re ≤ A * B := by
    have inner : ∀ x, ∑ y, p.prob y * (P * Q x * P * ρ y).trace.re ≤ A * B := by
      intro x
      rw [avg_lin]
      have e : (P * Q x * P * ρbar).trace = (Q x * (P * ρbar * P)).trace := by
        simp only [Matrix.mul_assoc]
        rw [trace_mul_comm P]
        simp only [Matrix.mul_assoc]
      rw [e]
      have h := trace_mul_psd_nonneg _ _ (proj_psd (hQ x)) hsandwich
      simp only [mul_sub, trace_sub, mul_smul_comm, mul_one, trace_smul, Complex.sub_re,
        Complex.smul_re, smul_eq_mul, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re] at h
      have := hsize x
      nlinarith
    calc ∑ x, ∑ y, p.prob x * p.prob y * (P * Q x * P * ρ y).trace.re
        = ∑ x, p.prob x * ∑ y, p.prob y * (P * Q x * P * ρ y).trace.re := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ x, p.prob x * (A * B) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (inner x) (p.nonneg x)
      _ = A * B := by rw [← Finset.sum_mul, p.sum_eq_one, one_mul]
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  set L : ℝ := 1 - 17 * ε - 4 * ((M:ℝ) - 1) * A * B with hL
  have avg_m : ∀ m : Fin M, L ≤ ∑ C : Fin M → J, codeWeight p C *
      ((decoderK P (Q ∘ C) m) * ρ (C m) * (decoderK P (Q ∘ C) m)ᴴ).trace.re := by
    intro m
    set F := Finset.univ.filter (fun i : Fin M => i.val < m.val) with hF
    have hFne : ∀ i ∈ F, i ≠ m := by
      intro i hi h
      rw [hF, Finset.mem_filter, h] at hi
      exact lt_irrefl _ hi.2
    have hcard : (F.card : ℝ) ≤ (M:ℝ) - 1 := by
      have h1 : F ⊆ Finset.univ.erase m := fun i hi =>
        Finset.mem_erase.mpr ⟨hFne i hi, Finset.mem_univ i⟩
      have h2 := Finset.card_le_card h1
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin] at h2
      have : ((M - 1 : ℕ) : ℝ) = (M:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast h2
    have hlow : ∀ C : Fin M → J, (P * ρ (C m)).trace.re
        - 4 * (P * (1 - Q (C m)) * P * ρ (C m)).trace.re
        - 4 * ∑ i ∈ F, (P * Q (C i) * P * ρ (C m)).trace.re ≤
        ((decoderK P (Q ∘ C) m) * ρ (C m) * (decoderK P (Q ∘ C) m)ᴴ).trace.re :=
      fun C => per_term P hP (Q ∘ C) (fun i => hQ (C i)) m (ρ (C m)) (hρ (C m)).1
    refine le_trans ?_ (le_trans (le_of_eq (avg_algebra p m F hFne
      (fun x => (P * ρ x).trace.re) (fun x => (P * (1 - Q x) * P * ρ x).trace.re)
      (fun x y => (P * Q x * P * ρ y).trace.re)).symm)
      (Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hlow C) (weight_nonneg p C)))
    rw [Finset.sum_const, nsmul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left cbar (Nat.cast_nonneg (α := ℝ) F.card)
    have h2 := mul_le_mul_of_nonneg_right hcard (mul_nonneg hA hB)
    rw [hL]
    nlinarith
  have part1 : (∑ C : Fin M → J, codeWeight p C * codeError ρ P Q C) ≤ 1 - L := by
    unfold codeError
    have e : ∀ C : Fin M → J, codeWeight p C * (1 - 1 / (M:ℝ) * ∑ m,
        ((decoderK P (Q ∘ C) m) * ρ (C m) * (decoderK P (Q ∘ C) m)ᴴ).trace.re) =
        codeWeight p C - 1 / (M:ℝ) * ∑ m, codeWeight p C *
        ((decoderK P (Q ∘ C) m) * ρ (C m) * (decoderK P (Q ∘ C) m)ᴴ).trace.re := by
      intro C; rw [← Finset.mul_sum]; ring
    rw [Finset.sum_congr rfl fun C _ => e C, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm, weight_sum]
    have hS := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun m _ => avg_m m
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
    have : L ≤ 1 / (M:ℝ) * ∑ m : Fin M, ∑ C : Fin M → J, codeWeight p C *
        ((decoderK P (Q ∘ C) m) * ρ (C m) * (decoderK P (Q ∘ C) m)ᴴ).trace.re := by
      rw [one_div, le_inv_mul_iff₀ hMpos]; linarith
    linarith
  have hbound : 1 - L ≤ 33*ε+4*((M : ℝ)-1)*A*B := by rw [hL]; linarith
  refine ⟨part1.trans hbound, ?_⟩
  by_contra hne
  push Not at hne
  have hex : ∃ C0 : Fin M → J, codeWeight p C0 ≠ 0 := by
    by_contra h0
    push Not at h0
    have := weight_sum (M := M) p
    simp [h0] at this
  obtain ⟨C0, hC0⟩ := hex
  have hpos : 0 < codeWeight p C0 := lt_of_le_of_ne (weight_nonneg p C0) (Ne.symm hC0)
  have hlt : ∑ C : Fin M → J, codeWeight p C * (33*ε+4*((M : ℝ)-1)*A*B) <
      ∑ C : Fin M → J, codeWeight p C * codeError ρ P Q C :=
    Finset.sum_lt_sum (fun C _ => mul_le_mul_of_nonneg_left (hne C).le (weight_nonneg p C))
      ⟨C0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hne C0) hpos⟩
  rw [← Finset.sum_mul, weight_sum, one_mul] at hlt
  linarith [part1.trans hbound]
