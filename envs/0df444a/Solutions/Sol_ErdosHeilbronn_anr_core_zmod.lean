-- Prove2me | solution 1 for ErdosHeilbronn.anr_core_zmod
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T08:35:30.474958+00:00
-- url     : https://prove2.me/submissions/f8cab041-4bd0-4577-81a2-873b09d359b8

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace ErdosHeilbronn

open MvPolynomial Finset

section Field

variable {F : Type*} [Field F]

/-- The multi-index `(i, j)` on `Fin 2`. -/
noncomputable def idx (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

theorem idx_apply (i j : ℕ) (k : Fin 2) :
    idx i j k = if k = 0 then i else j := by
  fin_cases k <;> simp [idx, Finsupp.single_apply]

@[simp] theorem idx_apply_zero (i j : ℕ) : idx i j 0 = i := by simp [idx_apply]

@[simp] theorem idx_apply_one (i j : ℕ) : idx i j 1 = j := by simp [idx_apply]

theorem idx_eq (i j : ℕ) : idx i j = Finsupp.single 0 i + Finsupp.single 1 j := rfl

theorem degree_single (k : Fin 2) (v : ℕ) : Finsupp.degree (Finsupp.single k v) = v := by
  rcases v with _ | v
  · rw [Finsupp.single_zero k, map_zero]
  · rw [Finsupp.degree_apply, Finsupp.support_single_ne_zero _ (by omega), Finset.sum_singleton,
      Finsupp.single_apply, if_pos rfl]

@[simp] theorem degree_idx (i j : ℕ) : Finsupp.degree (idx i j) = i + j := by
  rw [idx_eq, map_add, degree_single, degree_single]

theorem idx_add_single_zero (i j : ℕ) : idx i j + Finsupp.single 0 1 = idx (i + 1) j := by
  ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_apply]

theorem idx_add_single_one (i j : ℕ) : idx i j + Finsupp.single 1 1 = idx i (j + 1) := by
  ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_apply]

/-- The binomial expansion of `(X 0 + X 1)^N` as a sum of monomials. -/
theorem pow_add_sum (N : ℕ) :
    (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ N
      = ∑ i ∈ range (N + 1),
          (N.choose i : F) • monomial (idx i (N - i)) (1 : F) := by
  induction N with
  | zero =>
      have h0 : idx 0 0 = 0 := by ext k : 1 <;> fin_cases k <;> simp [idx_apply]
      rw [pow_zero, Finset.sum_range_one, Nat.sub_self, h0]
      simp
  | succ N ih =>
      have hterm : ∀ i ∈ range (N + 1),
          ((N.choose i : F) • monomial (idx i (N - i)) (1 : F)) * (X 0 + X 1)
            = (N.choose i : F) • monomial (idx (i + 1) (N - i)) (1 : F)
              + (N.choose i : F) • monomial (idx i (N - i + 1)) (1 : F) := by
        intro i _
        rw [mul_add, smul_mul_assoc, smul_mul_assoc]
        rw [show (X 0 : MvPolynomial (Fin 2) F) = monomial (Finsupp.single 0 1) 1 from rfl,
          monomial_mul, idx_add_single_zero, one_mul]
        rw [show (X 1 : MvPolynomial (Fin 2) F) = monomial (Finsupp.single 1 1) 1 from rfl,
          monomial_mul, idx_add_single_one, one_mul]
      have hshift : ∀ j ∈ range N, (N.choose (j + 1) : F) • monomial (idx (j + 1) (N - (j + 1) + 1)) (1 : F)
          = (N.choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F) := by
        intro j hj
        have h1 : N - (j + 1) + 1 = N - j := by
          have := Finset.mem_range.mp hj
          omega
        rw [h1]
      have hpascal : ∀ j ∈ range N, ((N + 1).choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F)
          = (N.choose j : F) • monomial (idx (j + 1) (N - j)) (1 : F)
            + (N.choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F) := by
        intro j _
        rw [Nat.choose_succ_succ', Nat.cast_add, add_smul]
      rw [pow_succ, ih, Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have eA : ∑ i ∈ range (N + 1), (N.choose i : F) • monomial (idx (i + 1) (N - i)) (1 : F)
          = ∑ j ∈ range N, (N.choose j : F) • monomial (idx (j + 1) (N - j)) (1 : F)
            + monomial (idx (N + 1) 0) (1 : F) := by
        rw [Finset.sum_range_succ]
        simp [Nat.choose_self]
      have eB : ∑ i ∈ range (N + 1), (N.choose i : F) • monomial (idx i (N - i + 1)) (1 : F)
          = monomial (idx 0 (N + 1)) (1 : F)
            + ∑ j ∈ range N, (N.choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F) := by
        rw [Finset.sum_range_succ']
        rw [Finset.sum_congr rfl hshift]
        simp
        ac_rfl
      have eC : ∑ j ∈ range (N + 2), ((N + 1).choose j : F) • monomial (idx j (N + 1 - j)) (1 : F)
          = (monomial (idx 0 (N + 1)) (1 : F)
              + (∑ j ∈ range N, (N.choose j : F) • monomial (idx (j + 1) (N - j)) (1 : F)
                + ∑ j ∈ range N, (N.choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F)))
            + monomial (idx (N + 1) 0) (1 : F) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        rw [show ∑ j ∈ range N, ((N + 1).choose (j + 1) : F) • monomial (idx (j + 1) (N + 1 - (j + 1))) (1 : F)
            = ∑ j ∈ range N, ((N + 1).choose (j + 1) : F) • monomial (idx (j + 1) (N - j)) (1 : F) from by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have h2 : N + 1 - (j + 1) = N - j := by
            have := Finset.mem_range.mp hj
            omega
          rw [h2]]
        rw [Finset.sum_congr rfl hpascal]
        rw [Finset.sum_add_distrib]
        simp
        ac_rfl
      rw [eA, eB, eC]
      abel

/-- Coefficient of `monomial (i, j)` in `(X 0 + X 1)^N`. -/
theorem coeff_pow_add (i j N : ℕ) (h : i + j = N) :
    coeff (idx i j) ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ N) = (N.choose i : F) := by
  rw [pow_add_sum, coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [show N - i = j from by omega]
    simp
  · intro b _ hb
    rw [smul_monomial, coeff_monomial]
    have : idx b (N - b) ≠ idx i j := by
      intro heq
      apply hb
      have := congrArg (fun t => t 0) heq
      simpa using this
    rw [if_neg this]
  · intro hi
    exact absurd (Finset.mem_range.mpr (by omega)) hi

end Field

section ANR

variable {F : Type*} [Field F] [DecidableEq F]

/-- Shift lemma: multiplying by `X 1` and reading off the coefficient. -/
theorem coeff_X1_mul (W : MvPolynomial (Fin 2) F) (k₁ k₂ : ℕ) (h : 1 ≤ k₂) :
    coeff (idx k₁ k₂) (X 1 * W) = coeff (idx k₁ (k₂ - 1)) W := by
  have hid : Finsupp.single (1 : Fin 2) 1 + idx k₁ (k₂ - 1) = idx k₁ k₂ := by
    ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_apply] <;> omega
  rw [show (X 1 : MvPolynomial (Fin 2) F) = monomial (Finsupp.single 1 1) 1 from rfl,
    ← hid, coeff_monomial_mul, one_mul]

/-- Shift lemma: multiplying by `X 0`. -/
theorem coeff_X0_mul (W : MvPolynomial (Fin 2) F) (k₁ k₂ : ℕ) (h : 1 ≤ k₁) :
    coeff (idx k₁ k₂) (X 0 * W) = coeff (idx (k₁ - 1) k₂) W := by
  have hid : Finsupp.single (0 : Fin 2) 1 + idx (k₁ - 1) k₂ = idx k₁ k₂ := by
    ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_apply] <;> omega
  rw [show (X 0 : MvPolynomial (Fin 2) F) = monomial (Finsupp.single 0 1) 1 from rfl,
    ← hid, coeff_monomial_mul, one_mul]

/-- Master absorption identity: `j * C(n, j) = (n - j + 1) * C(n, j-1)`. -/
theorem choose_absorb (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    j * n.choose j = (n - j + 1) * n.choose (j - 1) := by
  have hn : 1 ≤ n := le_trans hj hjn
  have e1 : j * n.choose j = n * (n - 1).choose (j - 1) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    rw [show n - 1 + 1 = n from by omega, show j - 1 + 1 = j from by omega] at h
    simp only [Nat.mul_comm] at h ⊢
    exact h.symm
  have e2 : (n - j + 1) * n.choose (j - 1)
      = n * (n - 1).choose (n - j) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (n - j)
    rw [show n - 1 + 1 = n from by omega] at h
    rw [Nat.choose_symm_of_eq_add (n := n) (a := j - 1) (b := n - j + 1) (by omega)]
    simp only [Nat.mul_comm] at h ⊢
    exact h.symm
  rw [e1, e2, Nat.choose_symm_of_eq_add (n := n - 1) (a := n - j) (b := j - 1) (by omega)]

/-- The two-set absorption used for distinct sizes. -/
theorem choose_absorb_two (k₁ k₂ : ℕ) (h1 : 1 ≤ k₁) (h2 : 1 ≤ k₂) :
    k₁ * (k₁ + k₂ - 1).choose k₁ = k₂ * (k₁ + k₂ - 1).choose (k₁ - 1) := by
  rw [choose_absorb (k₁ + k₂ - 1) k₁ h1 (by omega)]
  congr 1
  omega

/-- The vanishing remainder: the product over a nonempty value set differs from
`(x + y) ^ |C|` by a polynomial of total degree `< |C|`. -/
theorem prod_sub_pow_deg : ∀ (C : Finset F), C.Nonempty →
    ((∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c))
        - (X 0 + X 1) ^ (C.card : ℕ)).totalDegree < C.card := by
  intro C
  induction C using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert c₀ C h₀ ih =>
    have hcard : (insert c₀ C).card = C.card + 1 := Finset.card_insert_of_notMem h₀
    intro hne
    rcases Finset.eq_empty_or_nonempty C with rfl | hCne
    · rw [Finset.prod_insert h₀, Finset.prod_empty, mul_one, hcard, Finset.card_empty,
        pow_one]
      have hz : ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c₀) - (X 0 + X 1)
          = -MvPolynomial.C c₀ := by ring
      rw [hz, MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]
      omega
    · have ihR := ih hCne
      have hTDxy : ((X 0 + X 1 : MvPolynomial (Fin 2) F)).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
        simp [MvPolynomial.totalDegree_X]
      have hTDc : ((X 0 + X 1 : MvPolynomial (Fin 2) F)
          - MvPolynomial.C c₀).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        simp only [MvPolynomial.totalDegree_C, Nat.max_zero]
        exact hTDxy
      have hTDpow : ∀ n : ℕ,
          ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ n).totalDegree ≤ n := by
        intro n
        refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
        nlinarith [hTDxy]
      have hsplit :
          (∏ x ∈ insert c₀ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C x))
              - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ ((insert c₀ C).card : ℕ)
            = -(MvPolynomial.C c₀) * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ)
              + ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c₀)
                * ((∏ x ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C x))
                  - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ)) := by
        rw [Finset.prod_insert h₀, Finset.card_insert_of_notMem h₀, pow_succ]
        ring
      have h1 : (-(MvPolynomial.C c₀)
          * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ)).totalDegree ≤ C.card := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C, zero_add]
        exact hTDpow _
      have h2 : (((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c₀)
          * ((∏ x ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C x))
            - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ))).totalDegree ≤ C.card := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have hhh := add_le_add hTDc (le_of_lt ihR)
        omega
      rw [hsplit, hcard]
      have hfin := le_trans (MvPolynomial.totalDegree_add _ _) (max_le h1 h2)
      omega

end ANR

section Core

variable {F : Type*} [Field F] [DecidableEq F]

/-- The Alon–Nathanson–Ruzsa lemma, two variables: if `f ≠ 0` has degree at most
`k₁ + k₂` and the coefficient of `monomial (k₁, k₂)` in `f (x+y)^(k₁+k₂-deg f)` is
nonzero, then the set of sums `a + b` with `f(a,b) ≠ 0` has at least
`k₁ + k₂ - deg f + 1` elements. -/
theorem anr_core (A B : Finset F) (f : MvPolynomial (Fin 2) F) (hf : f ≠ 0)
    (k₁ k₂ : ℕ) (htA : k₁ + 1 = A.card) (htB : k₂ + 1 = B.card)
    (hdeg : f.totalDegree ≤ k₁ + k₂)
    (hc : coeff (idx k₁ k₂) (f * (X 0 + X 1) ^ (k₁ + k₂ - f.totalDegree)) ≠ 0) :
    (k₁ + k₂ - f.totalDegree + 1)
      ≤ (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hCdef⟩ : ∃ C : Finset F, C = (((A.product B).filter
          (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = k₁ + k₂ - f.totalDegree := ⟨_, rfl⟩
  rw [← hCdef] at hcon
  rw [← hK] at hc
  -- basic degree facts
  have hTDxy : ((X 0 + X 1 : MvPolynomial (Fin 2) F)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add (X 0) (X 1)) ?_
    simp [MvPolynomial.totalDegree_X]
  have hTDpow : ∀ n : ℕ, ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ n).totalDegree ≤ n := by
    intro n
    have h1 := MvPolynomial.totalDegree_pow ((X 0 + X 1 : MvPolynomial (Fin 2) F)) n
    nlinarith [hTDxy]
  have hTDfac : ∀ c : F, ((X 0 + X 1 : MvPolynomial (Fin 2) F)
      - MvPolynomial.C c).totalDegree ≤ 1 := by
    intro c
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    simp only [MvPolynomial.totalDegree_C, Nat.max_zero]
    exact hTDxy
  have hprodbound : (∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F)
      - MvPolynomial.C c)).totalDegree ≤ C.card := by
    calc (∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F)
          - MvPolynomial.C c)).totalDegree
        ≤ ∑ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c).totalDegree :=
          MvPolynomial.totalDegree_finsetProd C
            (fun c => (X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c)
      _ ≤ ∑ _c ∈ C, 1 := by exact Finset.sum_le_sum (fun c _ => hTDfac c)
      _ = C.card := by simp
  obtain ⟨Q, hQdef⟩ : ∃ Q : MvPolynomial (Fin 2) F, Q = (X 0 + X 1 : MvPolynomial (Fin 2) F)
      ^ (K - C.card) * ∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c) :=
    ⟨_, rfl⟩
  -- f·Q vanishes on the whole grid
  have hvanish : ∀ a ∈ A, ∀ b ∈ B, MvPolynomial.eval ![a, b] (f * Q) = 0 := by
    intro a ha b hb
    rw [MvPolynomial.eval_mul]
    by_cases hf0 : MvPolynomial.eval ![a, b] f = 0
    · rw [hf0, zero_mul]
    · have hmem : a + b ∈ C := by
        rw [hCdef]
        exact Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨ha, hb⟩, by simpa using hf0⟩, rfl⟩
      have hfac : MvPolynomial.eval ![a, b] ((X 0 + X 1 : MvPolynomial (Fin 2) F)
          - MvPolynomial.C (a + b)) = 0 := by simp
      have hprod0 : ∏ c ∈ C, (MvPolynomial.eval ![a, b]
          ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c)) = 0 :=
        Finset.prod_eq_zero hmem hfac
      rw [hQdef]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_prod,
        hprod0, mul_zero]
  -- the coefficient of monomial (k₁,k₂) in f·Q is still nonzero
  have hcoeff : coeff (idx k₁ k₂) (f * Q) ≠ 0 := by
    by_cases hC0 : C = ∅
    · rw [hC0] at hQdef hcon
      simp only [Finset.card_empty, Nat.sub_zero, Finset.prod_empty, mul_one] at hQdef hc
      rw [hQdef]
      exact hc
    · have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hC0
      have hproddeg := prod_sub_pow_deg C hCne
      obtain ⟨D, hDdef⟩ : ∃ D : MvPolynomial (Fin 2) F,
          D = Q - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ K := ⟨_, rfl⟩
      have hDsplit : D = (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card)
          * ((∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c))
            - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ)) := by
        have hKK : K - C.card + C.card = K := Nat.sub_add_cancel (by omega)
        rw [hDdef, hQdef,
          show (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ K
            = (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card + C.card) from by rw [hKK],
          pow_add]
        ring
      have hDdeg : D.totalDegree < K := by
        have h4 : (K - C.card) + C.card = K := Nat.sub_add_cancel (by omega)
        have h5 := hTDpow (K - C.card)
        rw [hDsplit]
        calc ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card)
              * ((∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c))
                - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ))).totalDegree
            ≤ ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card)).totalDegree
              + ((∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c))
                - (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (C.card : ℕ)).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ < (K - C.card) + C.card := add_lt_add_of_le_of_lt h5 hproddeg
          _ = K := h4
      have hzero : coeff (idx k₁ k₂) (f * D) = 0 := by
        apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        rw [← Finsupp.degree_apply, degree_idx]
        have h5 := MvPolynomial.totalDegree_mul f D
        have e1 : f.totalDegree + K ≤ k₁ + k₂ := by
          rw [hK]
          omega
        omega
      have hsplit2 : f * Q = f * ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ K) + f * D := by
        rw [hDdef]
        ring
      rw [hsplit2, coeff_add, hzero, add_zero]
      exact hc
  -- total degree of f·Q
  have hTDQ : Q.totalDegree ≤ K := by
    have h4 : (K - C.card) + C.card = K := Nat.sub_add_cancel (by omega)
    have h5 := hTDpow (K - C.card)
    rw [hQdef]
    calc ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card)
          * ∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c)).totalDegree
        ≤ ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ (K - C.card)).totalDegree
          + (∏ c ∈ C, ((X 0 + X 1 : MvPolynomial (Fin 2) F) - MvPolynomial.C c)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ (K - C.card) + C.card := by exact add_le_add h5 hprodbound
      _ = K := h4
  have hTDle : (f * Q).totalDegree ≤ k₁ + k₂ := by
    have h4 : f.totalDegree + K = k₁ + k₂ := by
      rw [hK]
      omega
    exact (le_trans (MvPolynomial.totalDegree_mul f Q)
      (add_le_add (le_refl _) hTDQ)).trans_eq h4
  have hTDge : Finsupp.degree (idx k₁ k₂) ≤ (f * Q).totalDegree := by
    rw [Finsupp.degree_apply]
    exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 hcoeff)
  -- CNS: a grid point where f·Q ≠ 0, contradicting vanishing
  have h0 : (idx k₁ k₂) 0 < A.card := by rw [idx_apply_zero]; omega
  have h1 : (idx k₁ k₂) 1 < B.card := by rw [idx_apply_one]; omega
  have htS : ∀ i, (idx k₁ k₂) i < ((![A, B] : Fin 2 → Finset F) i).card := by
    rw [Fin.forall_fin_two]
    exact ⟨h0, h1⟩
  obtain ⟨s, hs, hev⟩ := MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
    (f * Q) (idx k₁ k₂) hcoeff
    (le_antisymm (hTDle.trans_eq (degree_idx k₁ k₂).symm) hTDge) ![A, B] htS
  have hse : s = ![s 0, s 1] :=
    funext ((Fin.forall_fin_two (p := fun i => s i = (![s 0, s 1] : Fin 2 → F) i)).mpr ⟨rfl, rfl⟩)
  rw [hse] at hev
  exact absurd (hvanish (s 0) (hs 0) (s 1) (hs 1)) hev

end Core

end ErdosHeilbronn

theorem solution {p : ℕ} (hp : p.Prime)
    (A B : Finset (ZMod p)) (f : MvPolynomial (Fin 2) (ZMod p)) (hf : f ≠ 0)
    (k₁ k₂ : ℕ) (htA : k₁ + 1 = A.card) (htB : k₂ + 1 = B.card)
    (hdeg : MvPolynomial.totalDegree f ≤ k₁ + k₂)
    (hc : MvPolynomial.coeff (Finsupp.single 0 k₁ + Finsupp.single 1 k₂)
      (f * (MvPolynomial.X 0 + MvPolynomial.X 1) ^
        (k₁ + k₂ - MvPolynomial.totalDegree f)) ≠ 0) :
    (k₁ + k₂ - MvPolynomial.totalDegree f + 1)
      ≤ (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ErdosHeilbronn.anr_core A B f hf k₁ k₂ htA htB hdeg hc
