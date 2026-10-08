-- Prove2me | solution 1 for ErschlerZheng.exists_measure_mass_le_rpow_and_exp_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:37:50.22199+00:00
-- url     : https://prove2.me/submissions/309f7dcd-0495-411a-bdbc-14177ca362f8

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr
import Theorems.Thm_ErschlerZheng_satisfiesFr_five_firstString
import Theorems.Thm_ErschlerZheng_lengthL_firstString_le_three_mul_lambda0_pow
import Theorems.Thm_ErschlerZheng_two_mul_lengthL_le_lengthL_succ
import Theorems.Thm_ErschlerZheng_existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mono (S : Set G) {m n : ℕ} (h : m ≤ n) : Chou.wordBall S m ⊆ Chou.wordBall S n :=
  fun _ ⟨l, hl, hls, he⟩ => ⟨l, le_trans hl h, hls, he⟩

theorem wordBall_add_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S (m + n) ⊆ Chou.wordBall S m * Chou.wordBall S n := by
  rintro _ ⟨l, hl, hls, rfl⟩
  refine ⟨(l.take m).prod, ⟨l.take m, by simp, fun x hx => hls x (List.mem_of_mem_take hx), rfl⟩,
    (l.drop m).prod, ⟨l.drop m, by simp; omega, fun x hx => hls x (List.mem_of_mem_drop hx), rfl⟩,
    ?_⟩
  show (l.take m).prod * (l.drop m).prod = l.prod
  rw [← List.prod_append, List.take_append_drop]

/-- The letters: `1`, the elements of `S`, and their inverses. -/
def letters (S : Finset G) : Set G := insert 1 ((S : Set G) ∪ (S : Set G)⁻¹)

theorem letters_finite (S : Finset G) : (letters S).Finite :=
  ((S.finite_toSet.union S.finite_toSet.inv)).insert 1

theorem wordBall_one_subset (S : Finset G) : Chou.wordBall (S : Set G) 1 ⊆ letters S := by
  rintro _ ⟨l, hl, hls, rfl⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp [letters]
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rcases hls x (by simp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · simp at hl

theorem wordBall_finite (S : Finset G) (n : ℕ) : (Chou.wordBall (S : Set G) n).Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    rintro _ ⟨l, hl, -, rfl⟩
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    simp
  | succ n ih =>
    exact ((ih.mul (letters_finite S)).subset
      ((wordBall_add_subset _ n 1).trans (Set.mul_subset_mul_left (wordBall_one_subset S))))

end WordBallDev

end ErschlerZheng
end

section
/-!
# K2: Theorem A (Erschler–Zheng p. 2), from the goal Theorem 8.3

Apply the goal with `D = 5` (A16: `(012)^∞` satisfies `Fr(5)`) and `ε₁ = min ε (1/2)`. With
`L_n ⩽ 3λ_0^n` (K1), `L_{n+1} ⩾ 2L_n` (A18) and `λ_0^{α_0} = 2` (A19 gives `α_0 ∈ (0, 1)`), every
`x ∈ [1, L_{n+1}]` has `2^{(1−ε₁)n} ⩾ (3λ_0)^{−α_0} x^{α_0 − ε}`. For the tail, take `n` with
`L_n < r ⩽ L_{n+1}`; for the growth, `n` with `L_n ⩽ m < L_{n+1}`; radii below `L_1` are absorbed in
the constants (the ball of radius 1 has two elements, since the balls grow).
-/

namespace ErschlerZheng

namespace P5ThmADev

open Filter

set_option linter.unusedSectionVars false

lemma lengthL_zero (ω : ℕ → Fin 3) : lengthL ω 0 = 3 := by
  simp [lengthL, dotProduct]

lemma two_pow_le_lengthL (ω : ℕ → Fin 3) (n : ℕ) : 2 ^ n ≤ lengthL ω n := by
  induction n with
  | zero => rw [lengthL_zero]; norm_num
  | succ n ih =>
    have := two_mul_lengthL_le_lengthL_succ ω n
    rw [pow_succ]; omega

lemma lambda_alpha :
    1 < lambda0 ∧ 0 < alpha0 ∧ alpha0 < 1 ∧ lambda0 ^ alpha0 = 2 := by
  obtain ⟨-, ⟨hl0, -⟩, hα, -⟩ := existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM
  have hα1 := (abs_lt.mp hα).1
  have hα2 := (abs_lt.mp hα).2
  have hαpos : 0 < alpha0 := by linarith
  have hlog : 0 < Real.log lambda0 := by
    by_contra h
    push Not at h
    have : alpha0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg (by norm_num)) h
    linarith
  refine ⟨(Real.log_pos_iff hl0.le).mp hlog, hαpos, by linarith, ?_⟩
  rw [Real.rpow_def_of_pos hl0, alpha0, mul_div_cancel₀ _ hlog.ne', Real.exp_log (by norm_num)]

/-- `(3λ_0)^{−α_0} x^{α_0 − ε} ⩽ 2^{(1−ε₁)n}` for `1 ⩽ x ⩽ 3λ_0^{n+1}`. -/
lemma key_rpow {x ε ε₁ : ℝ} (hx : 1 ≤ x) (n : ℕ) (hxn : x ≤ 3 * lambda0 ^ (n + 1))
    (hε₁ : 0 < ε₁) (hε₁h : ε₁ ≤ 1 / 2) (hε₁ε : ε₁ ≤ ε) :
    (3 * lambda0) ^ (-alpha0) * x ^ (alpha0 - ε) ≤ (2 : ℝ) ^ ((1 - ε₁) * n) := by
  obtain ⟨hl1, hα0, hα1, hla⟩ := lambda_alpha
  have hl0 : 0 < lambda0 := by linarith
  have h3l : 1 ≤ 3 * lambda0 := by linarith
  -- `(x/(3λ))^α ⩽ 2^n`
  have h1 : (x / (3 * lambda0)) ^ alpha0 ≤ (2 : ℝ) ^ (n : ℝ) := by
    have hle : x / (3 * lambda0) ≤ lambda0 ^ n := by
      rw [div_le_iff₀ (by positivity)]
      calc x ≤ 3 * lambda0 ^ (n + 1) := hxn
        _ = lambda0 ^ n * (3 * lambda0) := by ring
    calc (x / (3 * lambda0)) ^ alpha0 ≤ (lambda0 ^ n) ^ alpha0 :=
          Real.rpow_le_rpow (by positivity) hle hα0.le
      _ = (2 : ℝ) ^ (n : ℝ) := by
          rw [← Real.rpow_natCast lambda0 n, ← Real.rpow_mul hl0.le, mul_comm,
            Real.rpow_mul hl0.le, hla]
  have h2 : (2 : ℝ) ^ ((1 - ε₁) * n) = ((2 : ℝ) ^ (n : ℝ)) ^ (1 - ε₁) := by
    rw [← Real.rpow_mul (by norm_num), mul_comm]
  have h3 : ((x / (3 * lambda0)) ^ alpha0) ^ (1 - ε₁) ≤ ((2 : ℝ) ^ (n : ℝ)) ^ (1 - ε₁) :=
    Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h4 : ((x / (3 * lambda0)) ^ alpha0) ^ (1 - ε₁) =
      x ^ (alpha0 * (1 - ε₁)) / (3 * lambda0) ^ (alpha0 * (1 - ε₁)) := by
    rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) (by positivity)]
  have h5 : x ^ (alpha0 - ε) ≤ x ^ (alpha0 * (1 - ε₁)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have h6 : (3 * lambda0) ^ (alpha0 * (1 - ε₁)) ≤ (3 * lambda0) ^ alpha0 :=
    Real.rpow_le_rpow_of_exponent_le h3l (by nlinarith)
  have h7 : (3 * lambda0) ^ (-alpha0) = ((3 * lambda0) ^ alpha0)⁻¹ :=
    Real.rpow_neg (by positivity) _
  rw [h2, h7]
  refine le_trans ?_ (h4 ▸ h3)
  rw [inv_mul_eq_div]
  have hpos1 : 0 < (3 * lambda0) ^ (alpha0 * (1 - ε₁)) := by positivity
  have hpos2 : 0 < (3 * lambda0) ^ alpha0 := by positivity
  have hx0 : 0 ≤ x ^ (alpha0 - ε) := by positivity
  calc x ^ (alpha0 - ε) / (3 * lambda0) ^ alpha0
      ≤ x ^ (alpha0 * (1 - ε₁)) / (3 * lambda0) ^ alpha0 := by gcongr
    _ ≤ x ^ (alpha0 * (1 - ε₁)) / (3 * lambda0) ^ (alpha0 * (1 - ε₁)) := by gcongr

lemma genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite := by
  have : (gens ω).Finite := by
    unfold gens
    exact (((Set.finite_singleton _).insert _).insert _).insert _
  exact this.preimage Subtype.val_injective.injOn

lemma wordBall_finite' (ω : ℕ → Fin 3) (n : ℕ) : (Chou.wordBall (genSet ω) n).Finite := by
  have h := WordBallDev.wordBall_finite (genSet_finite ω).toFinset n
  rwa [Set.Finite.coe_toFinset] at h

lemma growth_mono (ω : ℕ → Fin 3) {m n : ℕ} (h : m ≤ n) :
    growth (genSet ω) (m : ℝ) ≤ growth (genSet ω) (n : ℝ) := by
  unfold growth
  rw [Nat.floor_natCast, Nat.floor_natCast]
  exact Nat.card_mono (wordBall_finite' ω n) (WordBallDev.wordBall_mono _ h)

lemma two_le_growth_one (ω : ℕ → Fin 3) {N : ℕ} (hN : 1 < growth (genSet ω) (N : ℝ)) :
    2 ≤ growth (genSet ω) ((1 : ℕ) : ℝ) := by
  unfold growth at hN ⊢
  rw [Nat.floor_natCast] at hN ⊢
  -- a non-identity element of the ball of radius `N`
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ Chou.wordBall (genSet ω) N, g ≠ 1 := by
    by_contra h
    push Not at h
    have : Chou.wordBall (genSet ω) N ⊆ {1} := fun g hg => h g hg
    have h2 := Nat.card_mono (Set.finite_singleton _) this
    have h3 : Nat.card ({1} : Set (grigorchuk ω)) = 1 := Nat.card_unique
    omega
  obtain ⟨l, -, hl, rfl⟩ := hg
  obtain ⟨x, hxl, hx1⟩ : ∃ x ∈ l, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hg1 (List.prod_eq_one h)
  have hx : x ∈ Chou.wordBall (genSet ω) 1 := ⟨[x], by simp, by simpa using hl x hxl, by simp⟩
  have h1 : (1 : grigorchuk ω) ∈ Chou.wordBall (genSet ω) 1 := ⟨[], by simp, by simp, by simp⟩
  have hsub : ({1, x} : Set (grigorchuk ω)) ⊆ Chou.wordBall (genSet ω) 1 := by
    intro y hy
    rcases hy with rfl | rfl
    · exact h1
    · exact hx
  have := Nat.card_mono (wordBall_finite' ω 1) hsub
  rw [Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hx1)] at this
  exact this

lemma mass_le_one {G : Type*} {μ : G → ℝ} (hμ : IsProbability μ) (A : Set G) : mass μ A ≤ 1 := by
  unfold mass
  rw [← hμ.2.tsum_eq]
  exact (hμ.2.summable.indicator A).tsum_le_tsum
    (fun g => Set.indicator_le_self' (fun x _ => hμ.1 x) g) hμ.2.summable

lemma mass_mono {G : Type*} {μ : G → ℝ} (hμ : IsProbability μ) {A B : Set G} (h : A ⊆ B) :
    mass μ A ≤ mass μ B := by
  unfold mass
  exact (hμ.2.summable.indicator A).tsum_le_tsum
    (fun g => Set.indicator_le_indicator_of_subset h (fun x => hμ.1 x) g)
    (hμ.2.summable.indicator B)

end P5ThmADev

end ErschlerZheng
end

section
open ErschlerZheng
open P5ThmADev in
theorem solution :
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∃ μ : grigorchuk firstString → ℝ,
      IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧ HasFiniteEntropy μ ∧
        HasNontrivialPoissonBoundary μ ∧
        ∀ r : ℝ, 1 ≤ r →
          mass μ {g | r ≤ (wordLength (genSet firstString) g : ℝ)} ≤ C * r ^ (-alpha0 + ε)) ∧
    ∀ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      Real.exp (c * (n : ℝ) ^ (alpha0 - ε)) ≤ growth (genSet firstString) n := by
  obtain ⟨hl1, hα0, hα1, hla⟩ := lambda_alpha
  have hl0 : 0 < lambda0 := by linarith
  have hL1 : (1 : ℝ) ≤ lengthL firstString 1 := by
    have := two_pow_le_lengthL firstString 1
    exact_mod_cast (by omega : 1 ≤ lengthL firstString 1)
  have hK1 : ∀ n, (lengthL firstString n : ℝ) ≤ 3 * lambda0 ^ n :=
    lengthL_firstString_le_three_mul_lambda0_pow
  have hunb : ∀ x : ℝ, ∃ m : ℕ, x < lengthL firstString (m + 1) := by
    intro x
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, lt_of_lt_of_le hm ?_⟩
    have := two_pow_le_lengthL firstString (m + 1)
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := h2
      _ ≤ lengthL firstString (m + 1) := by exact_mod_cast this
  constructor
  · intro ε hε
    set ε₁ := min ε (1 / 2) with hε₁
    have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
    obtain ⟨C, hC, hgoal⟩ :=
      exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr 5 ε₁ hε₁0
    obtain ⟨μ, hnd, hsym, hpr, hfe, hnt, htail, -⟩ := hgoal firstString satisfiesFr_five_firstString
    set L1 := (lengthL firstString 1 : ℝ)
    refine ⟨C * (3 * lambda0) ^ alpha0 + L1 ^ alpha0, by positivity, μ, hnd, hsym, hpr, hfe, hnt,
      fun r hr => ?_⟩
    have hrpos : 0 < r := by linarith
    by_cases hrL : r ≤ L1
    · -- small radii: the trivial bound
      have h1 : L1 ^ (-alpha0) ≤ r ^ (-alpha0 + ε) := by
        calc L1 ^ (-alpha0) ≤ r ^ (-alpha0) :=
              Real.rpow_le_rpow_of_nonpos hrpos hrL (by linarith)
          _ ≤ r ^ (-alpha0 + ε) := Real.rpow_le_rpow_of_exponent_le hr (by linarith)
      have h2 : 1 ≤ L1 ^ alpha0 * r ^ (-alpha0 + ε) := by
        have : L1 ^ alpha0 * L1 ^ (-alpha0) = 1 := by
          rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
        have hL1a : 0 ≤ L1 ^ alpha0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 hL1a]
      have h3 : 0 ≤ C * (3 * lambda0) ^ alpha0 * r ^ (-alpha0 + ε) := by positivity
      calc mass μ {g | r ≤ (wordLength (genSet firstString) g : ℝ)} ≤ 1 := mass_le_one hpr _
        _ ≤ (C * (3 * lambda0) ^ alpha0 + L1 ^ alpha0) * r ^ (-alpha0 + ε) := by nlinarith
    · push Not at hrL
      -- `n` with `L_n < r ⩽ L_{n+1}`
      have hex : ∃ m : ℕ, r ≤ lengthL firstString (m + 1) :=
        (hunb r).imp fun m hm => hm.le
      classical
      obtain ⟨n, hn1, hmin⟩ : ∃ n, r ≤ lengthL firstString (n + 1) ∧
          ∀ j < n, ¬ r ≤ lengthL firstString (j + 1) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
      obtain _ | n' := n
      · exfalso
        have : r ≤ L1 := hn1
        linarith
      have hlt : (lengthL firstString (n' + 1) : ℝ) < r := by
        have := hmin n' (Nat.lt_succ_self n')
        push Not at this
        exact this
      have hsub : {g | r ≤ (wordLength (genSet firstString) g : ℝ)} ⊆
          (ball (genSet firstString) (lengthL firstString (n' + 1)))ᶜ := by
        intro g hg
        simp only [Set.mem_ofPred_eq] at hg
        simp only [ball, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
        linarith
      have hm := htail (n' + 1) (by omega)
      have hk := key_rpow hr (n' + 1) ((hn1.trans (hK1 _))) hε₁0 (min_le_right _ _)
        (min_le_left _ _)
      have h2neg : (2 : ℝ) ^ (-((1 - ε₁) * ((n' + 1 : ℕ) : ℝ))) =
          ((2 : ℝ) ^ ((1 - ε₁) * ((n' + 1 : ℕ) : ℝ)))⁻¹ := Real.rpow_neg (by norm_num) _
      have hpos : 0 < (3 * lambda0) ^ (-alpha0) * r ^ (alpha0 - ε) := by positivity
      have hinv : ((2 : ℝ) ^ ((1 - ε₁) * ((n' + 1 : ℕ) : ℝ)))⁻¹ ≤
          (3 * lambda0) ^ alpha0 * r ^ (-alpha0 + ε) := by
        have e1 : ((3 * lambda0) ^ (-alpha0) * r ^ (alpha0 - ε))⁻¹ =
            (3 * lambda0) ^ alpha0 * r ^ (-alpha0 + ε) := by
          rw [mul_inv, Real.rpow_neg (by positivity), inv_inv, ← Real.rpow_neg (by positivity)]
          congr 2; ring
        rw [← e1]
        exact inv_anti₀ hpos hk
      calc mass μ {g | r ≤ (wordLength (genSet firstString) g : ℝ)}
          ≤ mass μ (ball (genSet firstString) (lengthL firstString (n' + 1)))ᶜ := mass_mono hpr hsub
        _ ≤ C * (2 : ℝ) ^ (-((1 - ε₁) * ((n' + 1 : ℕ) : ℝ))) := hm
        _ ≤ C * ((3 * lambda0) ^ alpha0 * r ^ (-alpha0 + ε)) := by
            rw [h2neg]; exact mul_le_mul_of_nonneg_left hinv hC.le
        _ ≤ (C * (3 * lambda0) ^ alpha0 + L1 ^ alpha0) * r ^ (-alpha0 + ε) := by
            have : 0 ≤ L1 ^ alpha0 * r ^ (-alpha0 + ε) := by positivity
            nlinarith
  · intro ε hε
    set ε₁ := min ε (1 / 2) with hε₁
    have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
    obtain ⟨C, hC, hgoal⟩ :=
      exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr 5 ε₁ hε₁0
    obtain ⟨μ, -, -, -, -, -, -, c, hc, hgrow⟩ := hgoal firstString satisfiesFr_five_firstString
    set L1 := (lengthL firstString 1 : ℝ)
    have hg2 : 2 ≤ growth (genSet firstString) ((1 : ℕ) : ℝ) := by
      apply two_le_growth_one firstString (N := lengthL firstString 1)
      have h := hgrow 1 le_rfl
      have hpos : 0 < c * (2 : ℝ) ^ ((1 - ε₁) * ((1 : ℕ) : ℝ)) := by positivity
      have : (1 : ℝ) < Real.exp (c * (2 : ℝ) ^ ((1 - ε₁) * ((1 : ℕ) : ℝ))) :=
        Real.one_lt_exp_iff.mpr hpos
      exact_mod_cast this.trans_le h
    set c' := min (c * (3 * lambda0) ^ (-alpha0)) (Real.log 2 / L1 ^ alpha0) with hc'
    have hc'0 : 0 < c' := lt_min (by positivity) (by positivity)
    refine ⟨c', hc'0, fun m hm => ?_⟩
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    by_cases hmL : m < lengthL firstString 1
    · -- small radii
      have hmL' : (m : ℝ) ≤ L1 := by
        show (m : ℝ) ≤ (lengthL firstString 1 : ℝ)
        exact_mod_cast hmL.le
      have h1 : (m : ℝ) ^ (alpha0 - ε) ≤ L1 ^ alpha0 :=
        calc (m : ℝ) ^ (alpha0 - ε) ≤ (m : ℝ) ^ alpha0 :=
              Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
          _ ≤ L1 ^ alpha0 := Real.rpow_le_rpow (by positivity) hmL' hα0.le
      have h2 : c' * (m : ℝ) ^ (alpha0 - ε) ≤ Real.log 2 := by
        have hcl : c' ≤ Real.log 2 / L1 ^ alpha0 := min_le_right _ _
        have hL1a : 0 < L1 ^ alpha0 := by positivity
        calc c' * (m : ℝ) ^ (alpha0 - ε) ≤ Real.log 2 / L1 ^ alpha0 * L1 ^ alpha0 := by
              gcongr
          _ = Real.log 2 := div_mul_cancel₀ _ hL1a.ne'
      calc Real.exp (c' * (m : ℝ) ^ (alpha0 - ε)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h2
        _ = 2 := Real.exp_log (by norm_num)
        _ ≤ growth (genSet firstString) ((1 : ℕ) : ℝ) := by exact_mod_cast hg2
        _ ≤ growth (genSet firstString) (m : ℝ) := by exact_mod_cast growth_mono firstString hm
    · push Not at hmL
      classical
      have hex : ∃ j : ℕ, (m : ℝ) < lengthL firstString (j + 1) := hunb m
      obtain ⟨n, hn1, hmin⟩ : ∃ n, (m : ℝ) < lengthL firstString (n + 1) ∧
          ∀ j < n, ¬ (m : ℝ) < lengthL firstString (j + 1) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
      obtain _ | n' := n
      · exfalso
        have : (lengthL firstString 1 : ℝ) ≤ m := by exact_mod_cast hmL
        have h' : (m : ℝ) < lengthL firstString 1 := hn1
        linarith
      have hle : lengthL firstString (n' + 1) ≤ m := by
        have := hmin n' (Nat.lt_succ_self n')
        push Not at this
        exact_mod_cast this
      have hk := key_rpow hmR (n' + 1) (hn1.le.trans (hK1 _)) hε₁0 (min_le_right _ _)
        (min_le_left _ _)
      have hg := hgrow (n' + 1) (by omega)
      have hcc : c' ≤ c * (3 * lambda0) ^ (-alpha0) := min_le_left _ _
      have hm0 : 0 ≤ (m : ℝ) ^ (alpha0 - ε) := by positivity
      calc Real.exp (c' * (m : ℝ) ^ (alpha0 - ε))
          ≤ Real.exp (c * ((3 * lambda0) ^ (-alpha0) * (m : ℝ) ^ (alpha0 - ε))) := by
            apply Real.exp_le_exp.mpr
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hcc hm0
        _ ≤ Real.exp (c * (2 : ℝ) ^ ((1 - ε₁) * ((n' + 1 : ℕ) : ℝ))) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left hk hc.le
        _ ≤ growth (genSet firstString) (lengthL firstString (n' + 1) : ℝ) := hg
        _ ≤ growth (genSet firstString) (m : ℝ) := by exact_mod_cast growth_mono firstString hle
end
