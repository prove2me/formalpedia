-- Prove2me | solution 1 for ErdosHeilbronn.erdos_heilbronn
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:52:45.391104+00:00
-- url     : https://prove2.me/submissions/2be85638-74ca-488a-9d09-e2e53f612b94

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

section ZModApp

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Binomial coefficients below `p` never vanish in `ℤ/p`. -/
theorem choose_cast_ne_zero {n j : ℕ} (hp : p.Prime) (hn : n < p) (hj : j ≤ n) :
    (n.choose j : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ n.choose j := (ZMod.natCast_eq_zero_iff (n.choose j) p).mp h0
  have hfac := Nat.choose_mul_factorial_mul_factorial hj
  have hp : p.Prime := Fact.out
  have hnf : p ∣ n.factorial := by
    rw [← hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
  exact absurd ((Nat.Prime.dvd_factorial hp).mp hnf) (by omega)

/-- Coefficient of the `(y - x)(x+y)^N` leading monomial (distinct sizes). -/
theorem coeff_diff_pow (k₁ k₂ : ℕ) (hk1 : 1 ≤ k₁) (hk2 : 1 ≤ k₂) :
    coeff (idx k₁ k₂) ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))
      * (X 0 + X 1) ^ (k₁ + k₂ - 1))
      = ((k₁ + k₂ - 1).choose k₁ - (k₁ + k₂ - 1).choose (k₁ - 1) : ZMod p) := by
  have hN1 : k₁ + (k₂ - 1) = k₁ + k₂ - 1 := by omega
  have hN2 : (k₁ - 1) + k₂ = k₁ + k₂ - 1 := by omega
  have hsplit : ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))
      * ((X 0 + X 1) ^ (k₁ + k₂ - 1)))
      = X 1 * ((X 0 + X 1) ^ (k₁ + k₂ - 1)) - X 0 * ((X 0 + X 1) ^ (k₁ + k₂ - 1)) := by
    ring
  rw [hsplit, coeff_sub, coeff_X1_mul _ k₁ k₂ hk2, coeff_X0_mul _ k₁ k₂ hk1,
    coeff_pow_add _ _ _ hN1, coeff_pow_add _ _ _ hN2]

/-- Coefficient of the `(y - x)^2(x+y)^N` leading monomial (equal sizes). -/
theorem coeff_diff_sq_pow (q : ℕ) (hq : 2 ≤ q) :
    coeff (idx q q) (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2
      * (X 0 + X 1) ^ (q + q - 2))
      = ((q + q - 2).choose q - 2 * (q + q - 2).choose (q - 1)
          + (q + q - 2).choose (q - 2) : ZMod p) := by
  have hq1 : 1 ≤ q - 1 := by omega
  have e1 : q + (q - 1 - 1) = q + q - 2 := by omega
  have e2 : (q - 1) + (q - 1) = q + q - 2 := by omega
  have e3 : (q - 1 - 1) + q = q + q - 2 := by omega
  have hexp : (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2)
      * ((X 0 + X 1) ^ (q + q - 2))
      = X 1 * (X 1 * ((X 0 + X 1) ^ (q + q - 2)))
        - X 1 * (X 0 * ((X 0 + X 1) ^ (q + q - 2)))
        - X 0 * (X 1 * ((X 0 + X 1) ^ (q + q - 2)))
        + X 0 * (X 0 * ((X 0 + X 1) ^ (q + q - 2))) := by
    ring
  rw [hexp, coeff_add, coeff_sub, coeff_sub,
    coeff_X1_mul _ q q (by omega),
    coeff_X1_mul _ q (q - 1) hq1,
    coeff_X1_mul _ q q (by omega),
    coeff_X0_mul _ q (q - 1) (by omega),
    coeff_X0_mul _ q q (by omega),
    coeff_X1_mul _ (q - 1) q (by omega),
    coeff_X0_mul _ q q (by omega),
    coeff_X0_mul _ (q - 1) q hq1,
    coeff_pow_add _ _ _ e1, coeff_pow_add _ _ _ e2,
    coeff_pow_add _ _ _ e3]
  have hq2 : q - 1 - 1 = q - 2 := by omega
  rw [hq2]
  ring

/-- Nonvanishing for distinct sizes: `k₁ < k₂`, `k₁ + k₂ - 1 < p`. -/
theorem coeff_diff_pow_ne_zero {k₁ k₂ : ℕ} (hp : 3 ≤ p) (hk1 : 1 ≤ k₁) (hk2 : 1 ≤ k₂)
    (hlt : k₁ < k₂) (hsum : k₁ + k₂ + 1 ≤ p) :
    coeff (idx k₁ k₂) ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))
      * (X 0 + X 1) ^ (k₁ + k₂ - 1)) ≠ 0 := by
  have hpp : p.Prime := Fact.out
  intro h0
  rw [coeff_diff_pow k₁ k₂ hk1 hk2] at h0
  have habs := choose_absorb_two k₁ k₂ hk1 hk2
  -- cast the absorption into ℤ/p and use h0
  have hkey : (k₁ : ZMod p) * ((k₁ + k₂ - 1).choose k₁
      - (k₁ + k₂ - 1).choose (k₁ - 1))
      = ((k₂ - k₁ : ℕ) : ZMod p) * ((k₁ + k₂ - 1).choose (k₁ - 1) : ZMod p) := by
    have hcast : ((k₁ * (k₁ + k₂ - 1).choose k₁ : ℕ) : ZMod p)
        = ((k₂ * (k₁ + k₂ - 1).choose (k₁ - 1) : ℕ) : ZMod p) := by
      rw [habs]
    push_cast at hcast
    have hle : k₁ ≤ k₂ := by omega
    rw [Nat.cast_sub hle]
    linear_combination hcast
  rw [h0, mul_zero] at hkey
  have hn1 : (k₁ : ZMod p) ≠ 0 := by
    intro h1
    have hd := (ZMod.natCast_eq_zero_iff k₁ p).mp h1
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hn2 : ((k₂ - k₁ : ℕ) : ZMod p) ≠ 0 := by
    intro h2
    have hd := (ZMod.natCast_eq_zero_iff (k₂ - k₁) p).mp h2
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hn3 : ((k₁ + k₂ - 1).choose (k₁ - 1) : ZMod p) ≠ 0 :=
    choose_cast_ne_zero hpp (by omega) (by omega)
  exact (mul_ne_zero hn2 hn3) hkey.symm

/-- Nonvanishing for equal sizes: `q = k - 1 ≥ 2`, `2q + 1 ≤ p`. -/
theorem coeff_diff_sq_pow_ne_zero {q : ℕ} (hp : 3 ≤ p) (hq : 2 ≤ q)
    (hsum : q + q + 1 ≤ p) :
    coeff (idx q q) (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2
      * (X 0 + X 1) ^ (q + q - 2)) ≠ 0 := by
  have hpp : p.Prime := Fact.out
  intro h0
  rw [coeff_diff_sq_pow q hq] at h0
  have ha : q * (q + q - 2).choose q = (q - 1) * (q + q - 2).choose (q - 1) := by
    have h' := choose_absorb (q + q - 2) q (by omega) (by omega)
    rw [show q + q - 2 - q + 1 = q - 1 from by omega] at h'
    exact h'
  have hb : q * (q + q - 2).choose (q - 2) = (q - 1) * (q + q - 2).choose (q - 1) := by
    have h' := choose_absorb (q + q - 2) (q - 1) (by omega) (by omega)
    rw [show q + q - 2 - (q - 1) + 1 = q from by omega,
      show q - 1 - 1 = q - 2 from by omega] at h'
    exact h'.symm
  have hca : ((q * (q + q - 2).choose q : ℕ) : ZMod p)
      = (((q - 1) * (q + q - 2).choose (q - 1) : ℕ) : ZMod p) := by rw [ha]
  have hcb : ((q * (q + q - 2).choose (q - 2) : ℕ) : ZMod p)
      = (((q - 1) * (q + q - 2).choose (q - 1) : ℕ) : ZMod p) := by rw [hb]
  push_cast at hca hcb
  have hnorm : ((q - 1 : ℕ) : ZMod p) = (q : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast
    ring
  rw [hnorm] at hca hcb
  have hkey : (q : ZMod p) * (((q + q - 2).choose q : ZMod p)
      - 2 * ((q + q - 2).choose (q - 1) : ZMod p)
      + ((q + q - 2).choose (q - 2) : ZMod p))
      = (-2 : ZMod p) * ((q + q - 2).choose (q - 1) : ZMod p) := by
    linear_combination hca + hcb
  rw [h0, mul_zero] at hkey
  have h2n : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnC : ((q + q - 2).choose (q - 1) : ZMod p) ≠ 0 :=
    choose_cast_ne_zero hpp (by omega) (by omega)
  exact (mul_ne_zero (by simpa using h2n) hnC) hkey.symm

/-- The restricted sumset is symmetric. -/
theorem restricted_comm {A B : Finset (ZMod p)} :
    (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2))
      = (((B.product A).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)) := by
  ext x
  constructor
  · intro h
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hprod, hne⟩ := Finset.mem_filter.1 hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hprod
    refine Finset.mem_image.2 ⟨(ab.2, ab.1), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hb, ha⟩, by
        simp only [ne_eq]; exact fun h => hne h.symm⟩, ?_⟩
    rw [add_comm]
  · intro h
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hprod, hne⟩ := Finset.mem_filter.1 hab
    obtain ⟨hb, ha⟩ := Finset.mem_product.1 hprod
    refine Finset.mem_image.2 ⟨(ab.2, ab.1), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨ha, hb⟩, by
        simp only [ne_eq]; exact fun h => hne h.symm⟩, ?_⟩
    rw [add_comm]

/-- Evaluation of `X 1 - X 0` at `![a, b]` is `b - a`. -/
theorem eval_diff_iff (a b : ZMod p) :
    MvPolynomial.eval ![a, b] (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) ≠ 0 ↔ a ≠ b := by
  have h1 : MvPolynomial.eval ![a, b] (X 1 : MvPolynomial (Fin 2) (ZMod p)) = b := by simp
  have h2 : MvPolynomial.eval ![a, b] (X 0 : MvPolynomial (Fin 2) (ZMod p)) = a := by simp
  rw [MvPolynomial.eval_sub, h1, h2, sub_ne_zero]
  exact ne_comm

/-- Evaluation of `(X 1 - X 0)^2` at `![a, b]` is `(b - a)^2`. -/
theorem eval_diff_sq_iff (a b : ZMod p) :
    MvPolynomial.eval ![a, b] (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2) ≠ 0 ↔ a ≠ b := by
  have h1 : MvPolynomial.eval ![a, b] (X 1 : MvPolynomial (Fin 2) (ZMod p)) = b := by simp
  have h2 : MvPolynomial.eval ![a, b] (X 0 : MvPolynomial (Fin 2) (ZMod p)) = a := by simp
  rw [MvPolynomial.eval_pow, MvPolynomial.eval_sub, h1, h2]
  rw [show ((b - a)^2 ≠ 0) ↔ ((b - a) ≠ 0) from pow_ne_zero_iff (by norm_num), sub_ne_zero]
  exact ne_comm

/-- Transfer from the ANR value set to the restricted sumset. -/
theorem anr_to_restricted {A B : Finset (ZMod p)} {f : MvPolynomial (Fin 2) (ZMod p)}
    (hiff : ∀ a b : ZMod p, MvPolynomial.eval ![a, b] f ≠ 0 ↔ a ≠ b) {n : ℕ}
    (h : n ≤ (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
      (fun ab => ab.1 + ab.2)).card) :
    n ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  have hfil : ((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0))
      = ((A.product B).filter (fun ab => ab.1 ≠ ab.2)) := by
    ext ab
    simp only [Finset.mem_filter]
    constructor
    · intro hcon
      exact ⟨hcon.1, (hiff ab.1 ab.2).mp hcon.2⟩
    · intro hcon
      exact ⟨hcon.1, (hiff ab.1 ab.2).mpr hcon.2⟩
  rw [hfil] at h
  exact h

/-- Main theorem: the two-set Erdős–Heilbronn bound. -/
theorem restricted_sumset (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 3)
      ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  classical
  -- the polynomial-method case: |A| + |B| ≤ p + 1, both cards ≥ 2
  -- the polynomial-method case: |A| + |B| ≤ p + 1, both cards ≥ 2
  -- the polynomial-method case: |A| + |B| ≤ p + 1, both cards ≥ 2
  have hpoly : 2 ≤ A.card → 2 ≤ B.card → A.card + B.card ≤ p + 1 → A.card + B.card - 3
      ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
    intro hA2 hB2 hsum
    have hfz : (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) ≠ 0 := by
      intro h
      have h1 : MvPolynomial.eval ![0, 1]
          (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) = 0 := by rw [h]; simp
      rw [MvPolynomial.eval_sub] at h1
      simp at h1
    have hTDeq : (MvPolynomial.totalDegree (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) = 1 := by
      refine le_antisymm ?_ ?_
      · refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        simp only [MvPolynomial.totalDegree_X]
        simp
      · have h1 : MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)
            (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) = 1 := by
          have hX1 : (X 1 : MvPolynomial (Fin 2) (ZMod p))
              = MvPolynomial.monomial (Finsupp.single 1 1) 1 := rfl
          have hX0 : (X 0 : MvPolynomial (Fin 2) (ZMod p))
              = MvPolynomial.monomial (Finsupp.single 0 1) 1 := rfl
          rw [hX1, hX0, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
            MvPolynomial.coeff_monomial]
          have hne : ¬((Finsupp.single (0 : Fin 2) 1) = (Finsupp.single (1 : Fin 2) 1)) := by
            intro h
            have h2 := Finsupp.ext_iff.mp h (1 : Fin 2)
            simp only [Finsupp.single_apply] at h2
            norm_num at h2
          rw [if_pos rfl, if_neg hne]
          ring
        have hge : (Finsupp.single (1 : Fin 2) 1).sum (fun _ e => e)
            <= (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)).totalDegree :=
          MvPolynomial.le_totalDegree
            (MvPolynomial.mem_support_iff.2 (by rw [h1]; exact one_ne_zero))
        simp at hge
        exact hge
    rcases Nat.lt_trichotomy A.card B.card with hlt | heq | hgt
    · -- A.card < B.card: f = X 1 - X 0
      have hk1 : 1 ≤ A.card - 1 := by omega
      have hk2 : 1 ≤ B.card - 1 := by omega
      have hp3 : 3 ≤ p := by omega
      have hklt : A.card - 1 < B.card - 1 := by omega
      have hksum : (A.card - 1) + (B.card - 1) + 1 ≤ p := by omega
      have hc := coeff_diff_pow_ne_zero hp3 hk1 hk2 hklt hksum
      have hc' : coeff (idx (A.card - 1) (B.card - 1))
          ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) * (X 0 + X 1)
            ^ ((A.card - 1) + (B.card - 1)
              - MvPolynomial.totalDegree (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))) ≠ 0 := by
        rw [hTDeq]
        exact hc
      have hhtA : (A.card - 1) + 1 = A.card := by omega
      have hhtB : (B.card - 1) + 1 = B.card := by omega
      have hhdeg : MvPolynomial.totalDegree (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))
          ≤ (A.card - 1) + (B.card - 1) := by omega
      have hcore := anr_core A B (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) hfz
          (A.card - 1) (B.card - 1) hhtA hhtB hhdeg hc'
      have hres := anr_to_restricted (fun a b => eval_diff_iff a b) hcore
      rw [hTDeq] at hres
      omega
    · -- A.card = B.card: equal case, f = (X 1 - X 0)^2
      -- monomial decomposition of the square
      have hidx2 : Finsupp.single (1 : Fin 2) 1 + Finsupp.single 1 1 = idx 0 2 := by
        ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_add] <;> omega
      have hidx11a : Finsupp.single (1 : Fin 2) 1 + Finsupp.single 0 1 = idx 1 1 := by
        ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_add] <;> omega
      have hidx11b : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 = idx 1 1 := by
        ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_add] <;> omega
      have hidx20 : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 0 1 = idx 2 0 := by
        ext k : 1 <;> fin_cases k <;> simp [idx_apply, Finsupp.single_add] <;> omega
      have e2 : ((X 1 : MvPolynomial (Fin 2) (ZMod p))) * X 1 = monomial (idx 0 2) 1 := by
        rw [show (X 1 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 1 1) 1 from rfl,
          monomial_mul, hidx2, one_mul]
      have e3 : ((X 1 : MvPolynomial (Fin 2) (ZMod p))) * X 0 = monomial (idx 1 1) 1 := by
        rw [show (X 1 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 1 1) 1 from rfl,
          show (X 0 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 0 1) 1 from rfl,
          monomial_mul, hidx11a, one_mul]
      have e4 : ((X 0 : MvPolynomial (Fin 2) (ZMod p))) * X 1 = monomial (idx 1 1) 1 := by
        rw [show (X 1 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 1 1) 1 from rfl,
          show (X 0 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 0 1) 1 from rfl,
          monomial_mul, hidx11b, one_mul]
      have e5 : ((X 0 : MvPolynomial (Fin 2) (ZMod p))) * X 0 = monomial (idx 2 0) 1 := by
        rw [show (X 0 : MvPolynomial (Fin 2) (ZMod p)) = monomial (Finsupp.single 0 1) 1 from rfl,
          monomial_mul, hidx20, one_mul]
      have hexp : ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) * (X 1 - X 0)
          = X 1 * X 1 - X 1 * X 0 - X 0 * X 1 + X 0 * X 0 := by ring
      have hc02 : coeff (idx 0 2)
          (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) * (X 1 - X 0)) = 1 := by
        have hne1 : (idx 0 2 : Fin 2 →₀ ℕ) ≠ idx 1 1 := by
          intro h
          have h0 := congrArg (fun t => t 0) h
          simp only [idx_apply_zero] at h0
          norm_num at h0
        have hne2 : (idx 0 2 : Fin 2 →₀ ℕ) ≠ idx 2 0 := by
          intro h
          have h0 := congrArg (fun t => t 0) h
          simp only [idx_apply_zero] at h0
          norm_num at h0
        have hne1' : (idx 1 1 : Fin 2 →₀ ℕ) ≠ idx 0 2 := fun h => hne1 h.symm
        have hne2' : (idx 2 0 : Fin 2 →₀ ℕ) ≠ idx 0 2 := fun h => hne2 h.symm
        rw [hexp, e2, e3, e4, e5]
        simp only [coeff_add, coeff_sub, coeff_monomial, if_pos rfl, if_neg hne1',
          if_neg hne1', if_neg hne2']
        norm_num
      have hTDsq : (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) * (X 1 - X 0)).totalDegree = 2 := by
        refine le_antisymm ?_ ?_
        · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          nlinarith [hTDeq]
        · have hge : Finsupp.degree (idx 0 2)
              ≤ (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) * (X 1 - X 0)).totalDegree := by
            rw [Finsupp.degree_apply]
            exact MvPolynomial.le_totalDegree
              (MvPolynomial.mem_support_iff.2 (by rw [hc02]; exact one_ne_zero))
          rw [degree_idx] at hge
          exact hge
      have hfz2 : ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))) * (X 1 - X 0) ≠ 0 := by
        intro h
        rw [h] at hc02
        simp at hc02
      have hTDsq2 : MvPolynomial.totalDegree
          (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2) = 2 :=
        (congrArg MvPolynomial.totalDegree
          (sq (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))).trans hTDsq
      have hfz2' : ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2 ≠ 0 := by
        rw [sq]
        exact hfz2
      -- q := A.card - 1; the case q = 1 (cards = 2) is direct
      rcases Nat.lt_or_ge A.card 3 with hsmall | hbig3
      · -- cards = 2: some a ∈ A differs from a fixed b ∈ B, giving one restricted sum
        obtain ⟨b, hb⟩ := hB
        obtain ⟨a1, ha1, a2, ha2, ha12⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
        have hmem : (∃ a ∈ A, a ≠ b ∧ a + b ∈
            (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2))) := by
          by_cases h1b : a1 = b
          · have ha2b : a2 ≠ b := fun h => ha12 (h1b.trans h.symm)
            exact ⟨a2, ha2, ha2b, Finset.mem_image.2 ⟨(a2, b), Finset.mem_filter.2
              ⟨Finset.mem_product.2 ⟨ha2, hb⟩, ha2b⟩, rfl⟩⟩
          · exact ⟨a1, ha1, h1b, Finset.mem_image.2 ⟨(a1, b), Finset.mem_filter.2
              ⟨Finset.mem_product.2 ⟨ha1, hb⟩, h1b⟩, rfl⟩⟩
        obtain ⟨a, _, hab, hsum2⟩ := hmem
        have hcard1 : 1 ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image
            (fun ab => ab.1 + ab.2)).card := Finset.one_le_card.2 ⟨a + b, hsum2⟩
        have hpp : 2 ≤ p := hp.two_le
        omega
      · -- q ≥ 2: the ANR route with f = (X 1 - X 0)^2
        have hq : 2 ≤ A.card - 1 := by omega
        have hp3 : 3 ≤ p := by omega
        have hqsum : (A.card - 1) + (A.card - 1) + 1 ≤ p := by omega
        have hc := coeff_diff_sq_pow_ne_zero hp3 hq hqsum
        have hc' : coeff (idx (A.card - 1) (A.card - 1))
            (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2 * (X 0 + X 1)
              ^ ((A.card - 1) + (A.card - 1)
                - MvPolynomial.totalDegree
                  (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2))) ≠ 0 := by
          rw [hTDsq2]
          exact hc
        have hdeg' : MvPolynomial.totalDegree
            (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2)
            ≤ (A.card - 1) + (A.card - 1) := by omega
        have hhta : (A.card - 1) + 1 = A.card := by omega
        have hhtb : (A.card - 1) + 1 = B.card := by omega
        have hcore := anr_core A B (((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))^2) hfz2'
          (A.card - 1) (A.card - 1) hhta hhtb hdeg' hc'
        have hres := anr_to_restricted (fun a b => eval_diff_sq_iff a b) hcore
        rw [hTDsq2] at hres
        omega
    · -- B.card < A.card: swapped distinct case
      have hk1 : 1 ≤ B.card - 1 := by omega
      have hk2 : 1 ≤ A.card - 1 := by omega
      have hp3 : 3 ≤ p := by omega
      have hklt : B.card - 1 < A.card - 1 := by omega
      have hksum : (B.card - 1) + (A.card - 1) + 1 ≤ p := by omega
      have hc := coeff_diff_pow_ne_zero hp3 hk1 hk2 hklt hksum
      have hc' : coeff (idx (B.card - 1) (A.card - 1))
          ((X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) * (X 0 + X 1)
            ^ ((B.card - 1) + (A.card - 1)
              - MvPolynomial.totalDegree (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)))) ≠ 0 := by
        rw [hTDeq]
        exact hc
      have hhtA : (B.card - 1) + 1 = B.card := by omega
      have hhtB : (A.card - 1) + 1 = A.card := by omega
      have hhdeg : MvPolynomial.totalDegree (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p))
          ≤ (B.card - 1) + (A.card - 1) := by omega
      have hcore := anr_core B A (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)) hfz
          (B.card - 1) (A.card - 1) hhtA hhtB hhdeg hc'
      have hres := anr_to_restricted (fun a b => eval_diff_iff a b) hcore
      rw [hTDeq, restricted_comm] at hres
      omega
  -- outer case analysis
  -- Case 1: |A| = 1 (or |B| = 1): direct
  have hsingle : ∀ A' B' : Finset (ZMod p), A'.Nonempty → B'.Nonempty → A'.card = 1 →
      min p (A'.card + B'.card - 3)
        ≤ (((A'.product B').filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
    intro A' B' hA' hB' hA1
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    by_cases haB : a ∈ B'
    · have hcard : (((B'.erase a).image (fun b => a + b))).card = B'.card - 1 := by
        rw [Finset.card_image_of_injective _ (fun x y h => by
          rw [add_right_inj] at h; exact h)]
        rw [Finset.card_erase_of_mem haB]
      have hsub : (((B'.erase a).image (fun b => a + b)))
          ≤ (((({a} : Finset (ZMod p)).product B').filter (fun ab => ab.1 ≠ ab.2)).image
            (fun ab => ab.1 + ab.2)) := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
        refine Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨Finset.mem_singleton_self _, Finset.mem_of_mem_erase hb⟩,
            fun hab => (Finset.mem_erase.mp hb).1 hab.symm⟩, rfl⟩
      have hle := le_trans hcard.ge (Finset.card_le_card hsub)
      have hcs : (({a} : Finset (ZMod p))).card = 1 := Finset.card_singleton a
      omega
    · have hcard : (((B'.erase a).image (fun b => a + b))).card = B'.card := by
        rw [Finset.card_image_of_injective _ (fun x y h => by
          rw [add_right_inj] at h; exact h)]
        rw [Finset.erase_eq_of_notMem haB]
      have hsub : (((B'.erase a).image (fun b => a + b)))
          ≤ (((({a} : Finset (ZMod p)).product B').filter (fun ab => ab.1 ≠ ab.2)).image
            (fun ab => ab.1 + ab.2)) := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
        have hba : a ≠ b := by
          intro h
          rw [h] at haB
          exact haB (Finset.mem_erase.mp hb).2
        refine Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨Finset.mem_singleton_self _, Finset.mem_of_mem_erase hb⟩,
            hba⟩, rfl⟩
      have hle := le_trans hcard.ge (Finset.card_le_card hsub)
      have hcs : (({a} : Finset (ZMod p))).card = 1 := Finset.card_singleton a
      omega
  rcases Nat.lt_or_ge A.card 2 with hsmallA | hbigA
  · have hApos : 0 < A.card := Finset.card_pos.2 hA
    have hA1 : A.card = 1 := by omega
    exact hsingle A B hA hB hA1
  rcases Nat.lt_or_ge B.card 2 with hsmallB | hbigB
  · have hBpos : 0 < B.card := Finset.card_pos.2 hB
    have hsw := hsingle B A hB hA (by omega)
    rw [restricted_comm] at hsw
    omega
  -- both cards ≥ 2
  rcases Nat.Prime.eq_two_or_odd hp with hp2 | hpodd
  · -- p = 2: cards ≤ 2 so both = 2 = univ
    subst hp2
    have hunivA : A = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ A) ?_
      rw [Finset.card_univ, ZMod.card]
      omega
    have hunivB : B = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ B) ?_
      rw [Finset.card_univ, ZMod.card]
      omega
    have hmem : (1 : ZMod 2) ∈ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image
        (fun ab => ab.1 + ab.2)) := by
      refine Finset.mem_image.2 ⟨((0 : ZMod 2), 1), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨by rw [hunivA]; exact Finset.mem_univ _, by rw [hunivB]; exact Finset.mem_univ _⟩,
          (by norm_num : (0 : ZMod 2) ≠ 1)⟩, rfl⟩
    have hcard1 : 1 ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image
        (fun ab => ab.1 + ab.2)).card :=
      Finset.one_le_card.2 ⟨1, hmem⟩
    have hcA : A.card = 2 := by rw [hunivA, Finset.card_univ]; exact ZMod.card 2
    have hcB : B.card = 2 := by rw [hunivB, Finset.card_univ]; exact ZMod.card 2
    omega
  · -- p odd
    rcases Nat.lt_or_ge (A.card + B.card) (p + 2) with hle | hbig
    · exact le_trans (min_le_right p (A.card + B.card - 3)) (hpoly hbigA hbigB (by omega))
    · -- counting: A + B ≥ p + 2, every t has a restricted representation
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      have huniv : (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image
          (fun ab => ab.1 + ab.2)) = Finset.univ := by
        refine Finset.eq_univ_iff_forall.2 ?_
        intro t
        set Bt := B.image (fun b => t - b)
        have hBt : Bt.card = B.card := Finset.card_image_of_injective _
          (fun x y h => by rw [sub_right_inj] at h; exact h)
        have h1 := Finset.card_union_add_card_inter A Bt
        have h2 : (A ∪ Bt).card ≤ p := by
          calc (A ∪ Bt).card ≤ (Finset.univ : Finset (ZMod p)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = p := by rw [Finset.card_univ, ZMod.card]
        have h3 : 2 ≤ (A ∩ Bt).card := by omega
        -- an element a ∈ A ∩ Bt with 2a ≠ t
        have hex : ∃ a ∈ A ∩ Bt, a ≠ t - a := by
          by_contra hcon
          push_neg at hcon
          have hsub2 : (A ∩ Bt) ⊆ {(2 : ZMod p)⁻¹ * t} := by
            intro a ha
            have h2a : (2 : ZMod p) * a = t := by
              have hthis := hcon a ha
              linear_combination hthis
            have h2ne : (2 : ZMod p) ≠ 0 := by
              intro h0
              have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h0
              have hplt : p ≤ 2 := Nat.le_of_dvd (by omega) hd
              have hpge : 1 < p := hp.one_lt
              omega
            rw [Finset.mem_singleton, ← h2a, ← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
          have hle1 : (A ∩ Bt).card ≤ 1 :=
            le_trans (Finset.card_le_card hsub2) (by simp)
          exact absurd h3 (by omega)
        obtain ⟨a, ha, hane⟩ := hex
        obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 (Finset.mem_inter.1 ha).2
        have hbeq : t - b = a := hbe
        have hsum : a + b = t := by rw [← hbeq]; ring
        refine Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨(Finset.mem_inter.1 ha).1, hb⟩, ?_⟩, hsum⟩
        intro hab
        have hab' : a = b := hab
        rw [← hab'] at hbeq
        exact hane hbeq.symm
      rw [huniv, Finset.card_univ, ZMod.card]
      omega

/-- The Erdős–Heilbronn conjecture (h = 2): the restricted two-fold sumset of `A`
with itself has size at least `min(p, 2|A| - 3)`. -/
theorem erdos_heilbronn_core (hp : p.Prime) {A : Finset (ZMod p)} (hA : A.Nonempty) :
    min p (2 * A.card - 3)
      ≤ (((A.product A).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  have h := restricted_sumset hp hA hA
  have hcard : A.card + A.card = 2 * A.card := by omega
  rwa [hcard] at h



end ZModApp

/-- Restatement outside the instance section: the prime hypothesis carries everything,
so a top-level `solution` can call it in term mode without instance arguments. -/
theorem restricted_sumset_prime {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 3)
      ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact restricted_sumset hp hA hB

/-- Ditto for the corollary. -/
theorem erdos_heilbronn_prime {p : ℕ} (hp : p.Prime) {A : Finset (ZMod p)} (hA : A.Nonempty) :
    min p (2 * A.card - 3)
      ≤ (((A.product A).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact erdos_heilbronn_core hp hA

end ErdosHeilbronn


theorem solution {p : ℕ} (hp : p.Prime) {A : Finset (ZMod p)} (hA : A.Nonempty) :
    min p (2 * A.card - 3)
      ≤ (((A.product A).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card :=
  ErdosHeilbronn.erdos_heilbronn_prime hp hA
