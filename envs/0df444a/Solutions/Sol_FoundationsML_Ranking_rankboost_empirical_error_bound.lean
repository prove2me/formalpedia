-- Prove2me | solution 1 for FoundationsML.Ranking.rankboost_empirical_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T08:57:31.791584+00:00
-- url     : https://prove2.me/submissions/e5b191b5-2d7e-4377-8190-a21cc3fcef71

import Mathlib
import Definitions.Def_FoundationsML_Ranking_EmpiricalError
import Definitions.Def_FoundationsML_Ranking_RankBoostEnsemble
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonPlus
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonMinus

set_option autoImplicit false

namespace RB707

open FoundationsML.Ranking in
lemma u_cases {X : Type*} (a b : X) (yi : ℝ) (g : X → ℝ) (hy : yi = 1 ∨ yi = -1)
    (hg : ∀ x, g x = 0 ∨ g x = 1) :
    yi * (g b - g a) = 1 ∨ yi * (g b - g a) = -1 ∨ yi * (g b - g a) = 0 := by
  rcases hy with hy | hy <;> rcases hg a with ha | ha <;> rcases hg b with hb | hb <;>
    rw [hy, ha, hb] <;> norm_num

open FoundationsML.Ranking in
lemma alpha_identity (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Real.exp (-RankBoostAlpha p q) * p + Real.exp (RankBoostAlpha p q) * q
      = 2 * Real.sqrt (p * q) := by
  have hr0 : 0 < Real.exp (RankBoostAlpha p q) := Real.exp_pos _
  have hr2 : Real.exp (RankBoostAlpha p q) ^ 2 = p / q := by
    rw [← Real.exp_nat_mul]
    have : ((2:ℕ):ℝ) * RankBoostAlpha p q = Real.log (p / q) := by
      unfold RankBoostAlpha; push_cast; ring
    rw [this, Real.exp_log (div_pos hp hq)]
  rw [Real.exp_neg]
  generalize Real.exp (RankBoostAlpha p q) = r at hr0 hr2 ⊢
  have hp' : p = r ^ 2 * q := by
    rw [hr2]; field_simp
  have h1 : (r * q) ^ 2 = p * q := by rw [hp']; ring
  have hs : Real.sqrt (p * q) = r * q := by
    rw [← h1, Real.sqrt_sq (by positivity)]
  rw [hs, hp']
  field_simp
  ring

open FoundationsML.Ranking in
lemma round_sum {X : Type*} {m : ℕ} (D : Fin m → ℝ) (S1 S2 : Fin m → X) (y : Fin m → ℝ)
    (g : X → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hg : ∀ x, g x = 0 ∨ g x = 1)
    (hp : 0 < RankBoostWeightedEps D S1 S2 y g 1)
    (hq : 0 < RankBoostWeightedEps D S1 S2 y g (-1)) :
    ∑ i, D i * Real.exp (-RankBoostAlpha (RankBoostWeightedEps D S1 S2 y g 1)
        (RankBoostWeightedEps D S1 S2 y g (-1)) * y i * (g (S2 i) - g (S1 i)))
      = RankBoostNormalizer (RankBoostWeightedEps D S1 S2 y g 1)
          (RankBoostWeightedEps D S1 S2 y g (-1)) (RankBoostWeightedEps D S1 S2 y g 0) := by
  have key : ∀ (a : ℝ) (i : Fin m), D i * Real.exp (-a * y i * (g (S2 i) - g (S1 i))) =
      Real.exp (-a) * (D i * (if y i * (g (S2 i) - g (S1 i)) = 1 then (1:ℝ) else 0)) +
      Real.exp a * (D i * (if y i * (g (S2 i) - g (S1 i)) = -1 then (1:ℝ) else 0)) +
      D i * (if y i * (g (S2 i) - g (S1 i)) = 0 then (1:ℝ) else 0) := by
    intro a i
    have e : -a * y i * (g (S2 i) - g (S1 i)) = -a * (y i * (g (S2 i) - g (S1 i))) := by ring
    rw [e]
    rcases u_cases (S1 i) (S2 i) (y i) g (hy i) hg with hu | hu | hu <;> rw [hu] <;> norm_num <;>
      ring
  rw [Finset.sum_congr rfl (fun i _ => key _ i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  unfold RankBoostNormalizer
  rw [← alpha_identity _ _ hp hq]
  simp only [RankBoostWeightedEps]
  ring

open FoundationsML.Ranking in
lemma eps_total {X : Type*} {m : ℕ} (D : Fin m → ℝ) (S1 S2 : Fin m → X) (y : Fin m → ℝ)
    (g : X → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hg : ∀ x, g x = 0 ∨ g x = 1) :
    RankBoostWeightedEps D S1 S2 y g 1 + RankBoostWeightedEps D S1 S2 y g (-1)
      + RankBoostWeightedEps D S1 S2 y g 0 = ∑ i, D i := by
  simp only [RankBoostWeightedEps, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases u_cases (S1 i) (S2 i) (y i) g (hy i) hg with hu | hu | hu <;> rw [hu] <;> norm_num

lemma z_bound (p q w : ℝ) (hp : 0 < p) (hq : 0 < q) (hw : 0 ≤ w) (hs : p + q + w = 1) :
    w + 2 * Real.sqrt (p * q) ≤ Real.exp (-2 * ((p - q) / 2) ^ 2) := by
  have ha := Real.sq_sqrt hp.le
  have hb := Real.sq_sqrt hq.le
  have ha0 := Real.sqrt_nonneg p
  have hb0 := Real.sqrt_nonneg q
  rw [Real.sqrt_mul hp.le]
  generalize Real.sqrt p = a at ha ha0 ⊢
  generalize Real.sqrt q = b at hb hb0 ⊢
  subst ha hb
  have hexp := Real.add_one_le_exp (-2 * ((a ^ 2 - b ^ 2) / 2) ^ 2)
  have h2 : 0 ≤ 2 - (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  nlinarith [mul_nonneg (sq_nonneg (a - b)) h2]

open FoundationsML.Ranking in
lemma dist_succ {X : Type*} {m : ℕ} (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) (i : Fin m) :
    RankBoostDist S1 S2 y h (t + 1) i = RankBoostDist S1 S2 y h t i *
      Real.exp (-RankBoostAlpha (RankBoostEpsilonPlus S1 S2 y h t)
        (RankBoostEpsilonMinus S1 S2 y h t) * y i * (h t (S2 i) - h t (S1 i))) /
      RankBoostNormalizer (RankBoostEpsilonPlus S1 S2 y h t) (RankBoostEpsilonMinus S1 S2 y h t)
        (RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) 0) := by
  rfl

open FoundationsML.Ranking in
lemma dist_nonneg {X : Type*} {m : ℕ} (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) : ∀ i, 0 ≤ RankBoostDist S1 S2 y h t i := by
  induction t with
  | zero => intro i; simp only [RankBoostDist]; positivity
  | succ t ih =>
    intro i
    rw [dist_succ]
    have hW : 0 ≤ RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) 0 := by
      unfold RankBoostWeightedEps
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (ih j)
      split_ifs <;> norm_num
    apply div_nonneg
    · exact mul_nonneg (ih i) (Real.exp_pos _).le
    · unfold RankBoostNormalizer
      have := Real.sqrt_nonneg (RankBoostEpsilonPlus S1 S2 y h t * RankBoostEpsilonMinus S1 S2 y h t)
      linarith

open FoundationsML.Ranking in
lemma W0_nonneg {X : Type*} {m : ℕ} (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) : 0 ≤ RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) 0 := by
  unfold RankBoostWeightedEps
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (dist_nonneg S1 S2 y h t j)
  split_ifs <;> norm_num

open FoundationsML.Ranking in
lemma Z_pos {X : Type*} {m : ℕ} (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) (hp : 0 < RankBoostEpsilonPlus S1 S2 y h t)
    (hq : 0 < RankBoostEpsilonMinus S1 S2 y h t) :
    0 < RankBoostNormalizer (RankBoostEpsilonPlus S1 S2 y h t) (RankBoostEpsilonMinus S1 S2 y h t)
        (RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) 0) := by
  unfold RankBoostNormalizer
  have h1 := W0_nonneg S1 S2 y h t
  have h2 : 0 < Real.sqrt (RankBoostEpsilonPlus S1 S2 y h t * RankBoostEpsilonMinus S1 S2 y h t) :=
    Real.sqrt_pos.mpr (mul_pos hp hq)
  linarith

open FoundationsML.Ranking in
lemma dist_sum {X : Type*} {m : ℕ} (hm : 0 < m) (S1 S2 : Fin m → X) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (T : ℕ) (h : ℕ → X → ℝ)
    (hh : ∀ t < T, ∀ x, h t x = 0 ∨ h t x = 1)
    (hne : ∀ t < T, 0 < RankBoostEpsilonPlus S1 S2 y h t ∧
      0 < RankBoostEpsilonMinus S1 S2 y h t) :
    ∀ t ≤ T, ∑ i, RankBoostDist S1 S2 y h t i = 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [RankBoostDist]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  | succ t ih =>
    intro ht
    have htT : t < T := by omega
    simp only [dist_succ]
    rw [← Finset.sum_div]
    have hr := round_sum (RankBoostDist S1 S2 y h t) S1 S2 y (h t) hy (hh t htT)
      (hne t htT).1 (hne t htT).2
    have hZ := Z_pos S1 S2 y h t (hne t htT).1 (hne t htT).2
    unfold RankBoostEpsilonPlus RankBoostEpsilonMinus at hZ ⊢
    rw [hr]
    exact div_self hZ.ne'

open FoundationsML.Ranking in
lemma dist_closed {X : Type*} {m : ℕ} (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) (i : Fin m) :
    RankBoostDist S1 S2 y h t i = (1 / (m : ℝ)) * ∏ s ∈ Finset.range t,
      (Real.exp (-RankBoostAlpha (RankBoostEpsilonPlus S1 S2 y h s)
        (RankBoostEpsilonMinus S1 S2 y h s) * y i * (h s (S2 i) - h s (S1 i))) /
      RankBoostNormalizer (RankBoostEpsilonPlus S1 S2 y h s) (RankBoostEpsilonMinus S1 S2 y h s)
        (RankBoostWeightedEps (RankBoostDist S1 S2 y h s) S1 S2 y (h s) 0)) := by
  induction t with
  | zero => simp [RankBoostDist]
  | succ t ih =>
    rw [Finset.prod_range_succ, dist_succ, ih]
    ring

open FoundationsML.Ranking in
lemma err_le_prod {X : Type*} {m : ℕ} (hm : 0 < m) (S1 S2 : Fin m → X) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (T : ℕ) (h : ℕ → X → ℝ)
    (hh : ∀ t < T, ∀ x, h t x = 0 ∨ h t x = 1)
    (hne : ∀ t < T, 0 < RankBoostEpsilonPlus S1 S2 y h t ∧
      0 < RankBoostEpsilonMinus S1 S2 y h t) :
    EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
      ∏ s ∈ Finset.range T,
      RankBoostNormalizer (RankBoostEpsilonPlus S1 S2 y h s) (RankBoostEpsilonMinus S1 S2 y h s)
        (RankBoostWeightedEps (RankBoostDist S1 S2 y h s) S1 S2 y (h s) 0) := by
  set P := ∏ s ∈ Finset.range T,
      RankBoostNormalizer (RankBoostEpsilonPlus S1 S2 y h s) (RankBoostEpsilonMinus S1 S2 y h s)
        (RankBoostWeightedEps (RankBoostDist S1 S2 y h s) S1 S2 y (h s) 0) with hPdef
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro s hs
    have hs' : s < T := Finset.mem_range.mp hs
    exact Z_pos S1 S2 y h s (hne s hs').1 (hne s hs').2
  set E : Fin m → ℝ := fun i => ∑ s ∈ Finset.range T,
      (-RankBoostAlpha (RankBoostEpsilonPlus S1 S2 y h s)
        (RankBoostEpsilonMinus S1 S2 y h s) * y i * (h s (S2 i) - h s (S1 i))) with hEdef
  have hD : ∀ i, RankBoostDist S1 S2 y h T i * P = (1 / (m : ℝ)) * Real.exp (E i) := by
    intro i
    have hP0 : P ≠ 0 := hP.ne'
    rw [dist_closed, Finset.prod_div_distrib, ← Real.exp_sum, ← hPdef, mul_assoc,
      div_mul_cancel₀ _ hP0]
    try rfl
  have hE : ∀ i, E i = -(y i * (RankBoostEnsemble S1 S2 y h T (S2 i)
      - RankBoostEnsemble S1 S2 y h T (S1 i))) := by
    intro i
    simp only [hEdef, RankBoostEnsemble, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hind : ∀ i, (if y i ≠ 0 ∧ y i * (RankBoostEnsemble S1 S2 y h T (S2 i)
      - RankBoostEnsemble S1 S2 y h T (S1 i)) ≤ 0 then (1 : ℝ) else 0) ≤ Real.exp (E i) := by
    intro i
    split_ifs with hc
    · apply Real.one_le_exp
      rw [hE i]
      linarith [hc.2]
    · exact (Real.exp_pos _).le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T)
      ≤ (1 / (m : ℝ)) * ∑ i, Real.exp (E i) := by
        unfold EmpiricalError
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun i _ => hind i)
    _ = ∑ i, RankBoostDist S1 S2 y h T i * P := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => (hD i).symm)
    _ = P := by
        rw [← Finset.sum_mul, dist_sum hm S1 S2 y hy T h hh hne T le_rfl, one_mul]

end RB707

open FoundationsML.Ranking in
theorem solution {X : Type*} {m : ℕ} (hm : 0 < m)
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 0 ∨ h t x = 1)
    (hne : ∀ t < T, 0 < RankBoostEpsilonPlus S1 S2 y h t ∧
      0 < RankBoostEpsilonMinus S1 S2 y h t) :
    EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T,
          ((RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) ^ 2) ∧
      (∀ γ : ℝ, (∀ t < T, 0 < γ ∧
            γ ≤ (RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) →
        EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
          Real.exp (-2 * γ ^ 2 * T)) := by
  have hmain : EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
      Real.exp (-2 * ∑ t ∈ Finset.range T,
        ((RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) ^ 2) := by
    refine (RB707.err_le_prod hm S1 S2 y hy T h hh hne).trans ?_
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro s hs
      have hs' : s < T := Finset.mem_range.mp hs
      exact (RB707.Z_pos S1 S2 y h s (hne s hs').1 (hne s hs').2).le
    · intro s hs
      have hs' : s < T := Finset.mem_range.mp hs
      have htot := RB707.eps_total (RankBoostDist S1 S2 y h s) S1 S2 y (h s) hy (hh s hs')
      rw [RB707.dist_sum hm S1 S2 y hy T h hh hne s hs'.le] at htot
      unfold RankBoostNormalizer
      exact RB707.z_bound _ _ _ (hne s hs').1 (hne s hs').2 (RB707.W0_nonneg S1 S2 y h s) htot
  refine ⟨hmain, ?_⟩
  intro γ hγ
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  have hsum : (T : ℝ) * γ ^ 2 ≤ ∑ t ∈ Finset.range T,
      ((RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) ^ 2 := by
    have : ∑ t ∈ Finset.range T, γ ^ 2 = (T : ℝ) * γ ^ 2 := by
      simp [Finset.sum_const, Finset.card_range]
    rw [← this]
    apply Finset.sum_le_sum
    intro t ht
    have ht' : t < T := Finset.mem_range.mp ht
    obtain ⟨h0, h1⟩ := hγ t ht'
    exact pow_le_pow_left₀ h0.le h1 2
  nlinarith
