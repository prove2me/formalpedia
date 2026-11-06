-- Prove2me | solution 1 for CandesTao.CompletionII.matrix_completion_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T01:05:41.639996+00:00
-- url     : https://prove2.me/submissions/f182227d-0c7b-4aa5-9cab-ec8506691fd4

import Mathlib
import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_neumann
import Definitions.Def_CandesTao_Shared_StrongIncoherence
import Theorems.Thm_candes_recht_theorem41_bernoulli_tangent_sampling_concentration
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
import Theorems.Thm_dual_certificate_with_restricted_sampling_implies_unique_completion
import Theorems.Thm_bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
import Theorems.Thm_fixed_cardinality_completion_probability_from_bernoulli_model


set_option autoImplicit false

open MatrixCompletion
open scoped Classical BigOperators

theorem ctamp_prod_ins_out {α : Type*} [DecidableEq α] (p q : ℝ) {s t : Finset α} {x : α}
    (hx : x ∉ s) (ht : t ⊆ s) :
    (∏ y ∈ insert x s, if y ∈ t then p else q) = q * ∏ y ∈ s, if y ∈ t then p else q := by
  rw [Finset.prod_insert hx]
  have : x ∉ t := fun h => hx (ht h)
  simp [this]

theorem ctamp_prod_ins_in {α : Type*} [DecidableEq α] (p q : ℝ) {s t : Finset α} {x : α}
    (hx : x ∉ s) :
    (∏ y ∈ insert x s, if y ∈ insert x t then p else q) = p * ∏ y ∈ s, if y ∈ t then p else q := by
  rw [Finset.prod_insert hx]
  simp only [Finset.mem_insert, true_or, if_true]
  congr 1
  refine Finset.prod_congr rfl (fun y hy => ?_)
  have hyx : y ≠ x := fun h => hx (h ▸ hy)
  simp [hyx]

theorem ctamp_mass {α : Type*} [DecidableEq α] (p : ℝ) (s : Finset α) :
    (∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_powerset_insert hx]
    have h1 : (∑ t ∈ s.powerset, ∏ y ∈ insert x s, if y ∈ t then p else 1 - p)
        = (1 - p) * ∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      exact ctamp_prod_ins_out p (1 - p) hx (Finset.mem_powerset.mp ht)
    have h2 : (∑ t ∈ s.powerset, ∏ y ∈ insert x s, if y ∈ insert x t then p else 1 - p)
        = p * ∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      exact ctamp_prod_ins_in p (1 - p) hx
    rw [h1, h2, ih]; ring

theorem ctamp_coupling {α : Type*} [DecidableEq α] (a b : ℝ) (s : Finset α) :
    ∀ f : Finset α → ℝ,
    (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (t₁ ∪ t₂))
      = ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t := by
  induction s using Finset.induction_on with
  | empty => intro f; simp
  | insert x s hx ih =>
    intro f
    set A := ∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (t₁ ∪ t₂) with hA
    set B := ∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (insert x (t₁ ∪ t₂)) with hB
    have IA := ih f
    have IB := ih (fun t => f (insert x t))
    rw [← hA] at IA
    rw [← hB] at IB
    simp only [Finset.sum_powerset_insert hx, Finset.sum_add_distrib]
    have h1 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ t₂ then b else 1 - b)) * f (t₁ ∪ t₂))
        = (1 - a) * (1 - b) * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ h₁ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ h₂ => ?_)
      rw [ctamp_prod_ins_out a (1 - a) hx (Finset.mem_powerset.mp h₁),
        ctamp_prod_ins_out b (1 - b) hx (Finset.mem_powerset.mp h₂)]
      ring
    have h2 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ insert x t₂ then b else 1 - b)) * f (t₁ ∪ insert x t₂))
        = (1 - a) * b * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ h₁ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ _ => ?_)
      rw [ctamp_prod_ins_out a (1 - a) hx (Finset.mem_powerset.mp h₁),
        ctamp_prod_ins_in b (1 - b) hx, Finset.union_insert]
      ring
    have h3 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ insert x t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ t₂ then b else 1 - b)) * f (insert x t₁ ∪ t₂))
        = a * (1 - b) * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ h₂ => ?_)
      rw [ctamp_prod_ins_in a (1 - a) hx,
        ctamp_prod_ins_out b (1 - b) hx (Finset.mem_powerset.mp h₂), Finset.insert_union]
      ring
    have h4 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ insert x t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ insert x t₂ then b else 1 - b)) *
            f (insert x t₁ ∪ insert x t₂))
        = a * b * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ _ => ?_)
      rw [ctamp_prod_ins_in a (1 - a) hx, ctamp_prod_ins_in b (1 - b) hx,
        Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      ring
    have r1 : (∑ t ∈ s.powerset,
        (∏ y ∈ insert x s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t)
        = (1 - (a + b - a * b)) * ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [ctamp_prod_ins_out _ _ hx (Finset.mem_powerset.mp ht)]
      ring
    have r2 : (∑ t ∈ s.powerset,
        (∏ y ∈ insert x s, if y ∈ insert x t then (a + b - a * b) else 1 - (a + b - a * b)) *
          f (insert x t))
        = (a + b - a * b) * ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f (insert x t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [ctamp_prod_ins_in _ _ hx]
      ring
    rw [h1, h2, h3, h4, r1, r2, ← IA, ← IB]
    ring

theorem ctamp_weight_eq {n₁ n₂ : ℕ} (p : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) :
    bernoulliObservationWeight p Ω =
      ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ Ω then p else 1 - p := by
  unfold bernoulliObservationWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  · congr 1; ext y; simp
  · rw [Finset.filter_not, Finset.card_sdiff]
    simp [Finset.card_univ]

theorem ctamp_eventProb_eq {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p E =
      ∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if E t then 1 else 0) := by
  unfold bernoulliEventProb
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ctamp_weight_eq]
  split_ifs <;> simp

theorem ctamp_compl' {n₁ n₂ : ℕ} (p : ℝ) (E F : Finset (Fin n₁ × Fin n₂) → Prop)
    (hF : ∀ t, F t ↔ ¬ E t) :
    bernoulliEventProb p F = 1 - bernoulliEventProb p E := by
  rw [ctamp_eventProb_eq, ctamp_eventProb_eq]
  have hm := ctamp_mass p (Finset.univ : Finset (Fin n₁ × Fin n₂))
  have key : (∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if F t then (1 : ℝ) else 0)) +
      (∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if E t then (1 : ℝ) else 0)) =
      ∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : E t
    · have : ¬ F t := fun h' => (hF t).mp h' h
      simp [h, this]
    · have : F t := (hF t).mpr h
      simp [h, this]
  linarith [key, hm]

theorem ctamp_compl {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 - bernoulliEventProb p E :=
  ctamp_compl' p E (fun Ω => ¬ E Ω) (fun _ => Iff.rfl)

theorem ctamp_nonneg {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Fin n₁ × Fin n₂) → Prop) : 0 ≤ bernoulliEventProb p E := by
  rw [ctamp_eventProb_eq]
  refine Finset.sum_nonneg (fun t _ => mul_nonneg ?_ ?_)
  · exact Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  · split_ifs <;> norm_num

theorem ctamp_fail_mul {n₁ n₂ : ℕ} (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (F : Finset (Fin n₁ × Fin n₂) → Prop)
    (hF : ∀ Ω Ω' : Finset (Fin n₁ × Fin n₂), Ω ⊆ Ω' → F Ω' → F Ω) :
    bernoulliEventProb (a + b - a * b) F ≤ bernoulliEventProb a F * bernoulliEventProb b F := by
  rw [ctamp_eventProb_eq, ctamp_eventProb_eq, ctamp_eventProb_eq, Finset.sum_mul_sum,
    ← ctamp_coupling a b Finset.univ (fun t => if F t then 1 else 0)]
  refine Finset.sum_le_sum (fun t₁ _ => Finset.sum_le_sum (fun t₂ _ => ?_))
  have w1 : 0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a :=
    Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  have w2 : 0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b :=
    Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  have key : (if F (t₁ ∪ t₂) then (1 : ℝ) else 0) ≤
      (if F t₁ then 1 else 0) * (if F t₂ then 1 else 0) := by
    by_cases h : F (t₁ ∪ t₂)
    · have h1 : F t₁ := hF _ _ Finset.subset_union_left h
      have h2 : F t₂ := hF _ _ Finset.subset_union_right h
      simp [h, h1, h2]
    · simp only [h, if_false]
      split_ifs <;> norm_num
  calc ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a) *
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b)) *
        (if F (t₁ ∪ t₂) then (1 : ℝ) else 0)
      ≤ ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a) *
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b)) *
        ((if F t₁ then 1 else 0) * (if F t₂ then 1 else 0)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg w1 w2)
    _ = _ := by ring

theorem ctamp_fail_antitone {n₁ n₂ : ℕ} (q p : ℝ) (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Fin n₁ × Fin n₂) → Prop)
    (hE : ∀ Ω Ω' : Finset (Fin n₁ × Fin n₂), Ω ⊆ Ω' → E Ω → E Ω') :
    bernoulliEventProb p (fun Ω => ¬ E Ω) ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) := by
  rcases eq_or_lt_of_le (le_trans hqp hp1) with hq1 | hq1
  · have : p = q := by linarith
    rw [this]
  · set s := (p - q) / (1 - q) with hs
    have h1q : 0 < 1 - q := by linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith) h1q.le
    have hs1 : s ≤ 1 := by rw [hs, div_le_one h1q]; linarith
    have hps : q + s - q * s = p := by
      rw [hs]; field_simp; ring
    have hm := ctamp_fail_mul q s hq0 (le_trans hqp hp1) hs0 hs1 (fun Ω => ¬ E Ω)
      (fun Ω Ω' h hn hE' => hn (hE Ω Ω' h hE'))
    rw [hps] at hm
    have f0 : 0 ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) := ctamp_nonneg q hq0 (le_trans hqp hp1) _
    have f1 : bernoulliEventProb s (fun Ω => ¬ E Ω) ≤ 1 := by
      rw [ctamp_compl]; have := ctamp_nonneg s hs0 hs1 E; linarith
    calc bernoulliEventProb p (fun Ω => ¬ E Ω)
        ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) * bernoulliEventProb s (fun Ω => ¬ E Ω) := hm
      _ ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) * 1 := mul_le_mul_of_nonneg_left f1 f0
      _ = _ := mul_one _

theorem ctamp_sum4_comm {n r : ℕ} (H : Fin n → Fin n → Fin r → Fin r → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, H i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, H i j k l := by
  calc (∑ i, ∑ j, ∑ k, ∑ l, H i j k l) = ∑ i, ∑ k, ∑ j, ∑ l, H i j k l :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ k, ∑ l, ∑ j, H i j k l :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = ∑ k, ∑ i, ∑ l, ∑ j, H i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, H i j k l := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)

theorem ctamp_mu_sq {n r : ℕ} {M : RealMatrix n n} (S : SVD M r) (μ : ℝ)
    (hA : A1 S μ) (hn : 0 < n) (hr : 0 < r) : 1 ≤ μ ^ 2 := by
  have hE : ∀ i j, signMatrix S i j = ∑ k, S.u k i * S.v k j := by
    intro i j
    simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hsum : (∑ i, ∑ j, (signMatrix S i j) ^ 2) = (r : ℝ) := by
    calc (∑ i, ∑ j, (signMatrix S i j) ^ 2)
        = ∑ i, ∑ j, ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hE, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
          ring
      _ = ∑ k, ∑ l, ∑ i, ∑ j, (S.u k i * S.u l i) * (S.v k j * S.v l j) :=
          ctamp_sum4_comm _
      _ = ∑ k : Fin r, ∑ l : Fin r, (if k = l then (1 : ℝ) else 0) * (if k = l then 1 else 0) := by
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
          rw [← Finset.sum_mul_sum, S.u_orthonormal k l, S.v_orthonormal k l]
      _ = (r : ℝ) := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound : ∀ i j, (signMatrix S i j) ^ 2 ≤ μ ^ 2 * ((r : ℝ) / ((n : ℝ) * (n : ℝ))) := by
    intro i j
    have h1 := hA i j
    have h0 : 0 ≤ (r : ℝ) / ((n : ℝ) * (n : ℝ)) := by positivity
    have hs := Real.sq_sqrt h0
    have habs : |signMatrix S i j| ^ 2 ≤ (μ * Real.sqrt ((r : ℝ) / ((n : ℝ) * (n : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, hs] at habs
    exact habs
  have htot : (∑ i, ∑ j, (signMatrix S i j) ^ 2) ≤
      ∑ _i : Fin n, ∑ _j : Fin n, μ ^ 2 * ((r : ℝ) / ((n : ℝ) * (n : ℝ))) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
  rw [hsum] at htot
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have : (n : ℝ) * ((n : ℝ) * (μ ^ 2 * ((r : ℝ) / ((n : ℝ) * (n : ℝ))))) = μ ^ 2 * r := by
    field_simp
  rw [this] at htot
  nlinarith

/-! ## G1: golfing recursion (sequential union bound via the 2-set coupling) -/

theorem golf_sum_split {β : Type*} (s : Finset β) (a b g : β → ℝ) (h : β → β → ℝ) :
    (∑ t₁ ∈ s, ∑ t₂ ∈ s, (a t₁ * b t₂) * (g t₁ + h t₁ t₂)) =
      (∑ t₁ ∈ s, a t₁ * g t₁) * (∑ t₂ ∈ s, b t₂) +
        ∑ t₁ ∈ s, a t₁ * ∑ t₂ ∈ s, b t₂ * h t₁ t₂ := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t₁ _ => ?_)
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t₂ _ => ?_)
  ring

theorem ctamp_eventProb_eq' {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop)
    [DecidablePred E] :
    bernoulliEventProb p E =
      ∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if E t then 1 else 0) := by
  rw [ctamp_eventProb_eq]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : E t <;> simp [h]

theorem golf_rec_prob {n₁ n₂ : ℕ} {σ : Type*} (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P : σ → Prop) (step : Finset (Fin n₁ × Fin n₂) → σ → σ)
    (Good : Finset (Fin n₁ × Fin n₂) → σ → Prop)
    (Rec : ℕ → Finset (Fin n₁ × Fin n₂) → σ → Prop)
    (hP : ∀ t W, P W → P (step t W))
    (hbase : ∀ t W, P W → Rec 0 t W)
    (hstep : ∀ k t₁ t₂ W, P W → Good t₁ W → Rec k t₂ (step t₁ W) → Rec (k + 1) (t₁ ∪ t₂) W)
    (heps : ∀ W, P W → bernoulliEventProb q (fun t => ¬ Good t W) ≤ ε) :
    ∀ k : ℕ, ∀ W, P W →
      bernoulliEventProb (1 - (1 - q) ^ k) (fun t => ¬ Rec k t W) ≤ k * ε := by
  intro k
  induction k with
  | zero =>
    intro W hW
    have h0 : bernoulliEventProb (1 - (1 - q) ^ 0) (fun t => ¬ Rec 0 t W) = 0 := by
      unfold bernoulliEventProb
      refine Finset.sum_eq_zero (fun t _ => ?_)
      simp [hbase t W hW]
    rw [h0]; simp
  | succ k ih =>
    intro W hW
    have hqk0 : 0 ≤ 1 - (1 - q) ^ k := by
      have : (1 - q) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hqk1 : 1 - (1 - q) ^ k ≤ 1 := by
      have : 0 ≤ (1 - q) ^ k := pow_nonneg (by linarith) k
      linarith
    have hq' : 1 - (1 - q) ^ (k + 1) =
        q + (1 - (1 - q) ^ k) - q * (1 - (1 - q) ^ k) := by ring
    have hε0 : 0 ≤ ε := le_trans (ctamp_nonneg q hq0 hq1 _) (heps W hW)
    rw [hq', ctamp_eventProb_eq' _ (fun t => ¬ Rec (k + 1) t W)]
    have hc := ctamp_coupling q (1 - (1 - q) ^ k) Finset.univ
        (fun t => if ¬ Rec (k + 1) t W then (1 : ℝ) else 0)
    rw [← hc]
    have hw1 : ∀ t : Finset (Fin n₁ × Fin n₂),
        0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then q else 1 - q :=
      fun t => Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
    have hw2 : ∀ t : Finset (Fin n₁ × Fin n₂),
        0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)),
          if y ∈ t then (1 - (1 - q) ^ k) else 1 - (1 - (1 - q) ^ k) :=
      fun t => Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
    have hpt : ∀ t₁ t₂ : Finset (Fin n₁ × Fin n₂),
        (if ¬ Rec (k + 1) (t₁ ∪ t₂) W then (1 : ℝ) else 0) ≤
          (if ¬ Good t₁ W then 1 else 0) + (if ¬ Rec k t₂ (step t₁ W) then 1 else 0) := by
      intro t₁ t₂
      by_cases h1 : Rec (k + 1) (t₁ ∪ t₂) W
      · rw [if_neg (not_not.mpr h1)]
        split_ifs <;> norm_num
      · rw [if_pos h1]
        by_cases hg : Good t₁ W
        · have hr : ¬ Rec k t₂ (step t₁ W) := fun hr => h1 (hstep k t₁ t₂ W hW hg hr)
          rw [if_pos hr]; split_ifs <;> norm_num
        · rw [if_pos hg]; split_ifs <;> norm_num
    calc (∑ t₁ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
          ∑ t₂ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then q else 1 - q) *
              (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)),
                if y ∈ t₂ then (1 - (1 - q) ^ k) else 1 - (1 - (1 - q) ^ k))) *
              (fun t => if ¬ Rec (k + 1) t W then (1 : ℝ) else 0) (t₁ ∪ t₂))
        ≤ ∑ t₁ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
          ∑ t₂ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then q else 1 - q) *
              (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)),
                if y ∈ t₂ then (1 - (1 - q) ^ k) else 1 - (1 - (1 - q) ^ k))) *
              ((if ¬ Good t₁ W then (1 : ℝ) else 0) +
                (if ¬ Rec k t₂ (step t₁ W) then 1 else 0)) := by
          refine Finset.sum_le_sum (fun t₁ _ => Finset.sum_le_sum (fun t₂ _ => ?_))
          exact mul_le_mul_of_nonneg_left (hpt t₁ t₂) (mul_nonneg (hw1 t₁) (hw2 t₂))
      _ = (∑ t₁ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then q else 1 - q) *
              (if ¬ Good t₁ W then (1 : ℝ) else 0)) *
            (∑ t₂ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
              ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)),
                if y ∈ t₂ then (1 - (1 - q) ^ k) else 1 - (1 - (1 - q) ^ k)) +
          ∑ t₁ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then q else 1 - q) *
              ∑ t₂ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
                (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)),
                  if y ∈ t₂ then (1 - (1 - q) ^ k) else 1 - (1 - (1 - q) ^ k)) *
                  (if ¬ Rec k t₂ (step t₁ W) then 1 else 0) :=
          golf_sum_split _ _ _ _ _
      _ ≤ ε * 1 + ∑ t₁ ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then q else 1 - q) *
              ((k : ℝ) * ε) := by
          have hA := heps W hW
          rw [ctamp_eventProb_eq' _ (fun t => ¬ Good t W)] at hA
          rw [ctamp_mass]
          refine add_le_add (by linarith) (Finset.sum_le_sum (fun t₁ _ => ?_))
          refine mul_le_mul_of_nonneg_left ?_ (hw1 t₁)
          have hB := ih (step t₁ W) (hP t₁ W hW)
          rw [ctamp_eventProb_eq' _ (fun t => ¬ Rec k t (step t₁ W))] at hB
          exact hB
      _ = ((k + 1 : ℕ) : ℝ) * ε := by
          rw [← Finset.sum_mul, ctamp_mass]; push_cast; ring

/-! ## from fc5b8bdf_g4.lean -/
theorem g4_left_add {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    leftSingularProjection S (X + Y) = leftSingularProjection S X + leftSingularProjection S Y := by
  ext i j
  simp only [leftSingularProjection, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem g4_right_add {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    rightSingularProjection S (X + Y) = rightSingularProjection S X + rightSingularProjection S Y := by
  ext i j
  simp only [rightSingularProjection, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem g4_two_add {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    twoSidedSingularProjection S (X + Y) =
      twoSidedSingularProjection S X + twoSidedSingularProjection S Y := by
  ext i j
  simp only [twoSidedSingularProjection, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem g4_left_smul {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  ext i j
  simp only [leftSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem g4_right_smul {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  ext i j
  simp only [rightSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem g4_two_smul {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  ext i j
  simp only [twoSidedSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem g4_tp_add {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    tangentProjection S (X + Y) = tangentProjection S X + tangentProjection S Y := by
  unfold tangentProjection
  rw [g4_left_add, g4_right_add, g4_two_add]
  abel

theorem g4_tp_smul {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [g4_left_smul, g4_right_smul, g4_two_smul, smul_sub, smul_add]

theorem g4_tp_sub {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    tangentProjection S (X - Y) = tangentProjection S X - tangentProjection S Y := by
  have h : X - Y = X + (-1 : ℝ) • Y := by module
  rw [h, g4_tp_add, g4_tp_smul]
  (module)

theorem g4_np_add {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (X Y : RealMatrix n1 n2) :
    normalProjection S (X + Y) = normalProjection S X + normalProjection S Y := by
  unfold normalProjection
  rw [g4_tp_add]
  abel

theorem g4_spec_add {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold MatrixCompletion.spectralNorm
  rw [map_add, map_add]
  exact norm_add_le _ _

theorem g4_spec_nonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ MatrixCompletion.spectralNorm X := norm_nonneg _

theorem g4_frobSq_nonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq; positivity

theorem g4_spec_le_frob {n1 n2 : ℕ} (X : RealMatrix n1 n2) : MatrixCompletion.spectralNorm X ≤ frobeniusNorm X := by
  unfold MatrixCompletion.spectralNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
  rw [LinearMap.coe_toContinuousLinearMap']
  rw [← sq_le_sq₀ (norm_nonneg _) (by unfold frobeniusNorm; positivity)]
  rw [mul_pow, frobeniusNorm, Real.sq_sqrt (g4_frobSq_nonneg X), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.toEuclideanLin_apply, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.mulVec, dotProduct, PiLp.toLp_apply]
  unfold frobeniusNormSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem g4_frob_eq_norm {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    frobeniusNorm X = @Norm.norm _ (Matrix.frobeniusNormedAddCommGroup).toNorm X := by
  letI : NormedAddCommGroup (Matrix (Fin n1) (Fin n2) ℝ) := Matrix.frobeniusNormedAddCommGroup
  rw [Matrix.frobenius_norm_def, frobeniusNorm, frobeniusNormSq, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

theorem g4_frob_add {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    frobeniusNorm (X + Y) ≤ frobeniusNorm X + frobeniusNorm Y := by
  rw [g4_frob_eq_norm, g4_frob_eq_norm, g4_frob_eq_norm]
  letI : NormedAddCommGroup (Matrix (Fin n1) (Fin n2) ℝ) := Matrix.frobeniusNormedAddCommGroup
  exact norm_add_le X Y

theorem g4_frob_smul {n1 n2 : ℕ} (c : ℝ) (X : RealMatrix n1 n2) :
    frobeniusNorm (c • X) = |c| * frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem g4_frob_nonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _

theorem g4_frob_samp_le {n1 n2 : ℕ} (Ω : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    frobeniusNorm (samplingProjection Ω X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_)))
  simp only [samplingProjection]
  split_ifs <;> nlinarith [sq_nonneg (X i j)]

theorem g4_entry_nonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

/-- G4 step: one golfing batch. -/
theorem g4_step {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hnorm : ∀ X, spectralNorm (normalProjection S X) ≤ spectralNorm X)
    (q lam : ℝ) (hq : 0 < q) (hlam : 0 ≤ lam) (k : ℕ)
    (t₁ t₂ : Finset (Fin n1 × Fin n2)) (W : RealMatrix n1 n2)
    (hW : tangentProjection S W = W)
    (hF : frobeniusNorm (tangentProjection S (samplingProjection t₁ W) - q • W)
      ≤ (1 / 2) * q * frobeniusNorm W)
    (hE : entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t₁ W))
      ≤ (1 / 2) * entrySupNorm W)
    (hS : spectralNorm (centeredSamplingFluctuation t₁ q W) ≤ lam * entrySupNorm W)
    (Y' : RealMatrix n1 n2) (hY'v : VanishesOutside t₂ Y')
    (hY'f : frobeniusNorm (tangentProjection S (W - q⁻¹ • samplingProjection t₁ W)
        - tangentProjection S Y')
      ≤ (1 / 2) ^ k * frobeniusNorm (tangentProjection S (W - q⁻¹ • samplingProjection t₁ W)))
    (hY's : spectralNorm (normalProjection S Y')
      ≤ 2 * lam * entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t₁ W))) :
    VanishesOutside (t₁ ∪ t₂) (q⁻¹ • samplingProjection t₁ W + Y') ∧
    frobeniusNorm (W - tangentProjection S (q⁻¹ • samplingProjection t₁ W + Y'))
      ≤ (1 / 2) ^ (k + 1) * frobeniusNorm W ∧
    spectralNorm (normalProjection S (q⁻¹ • samplingProjection t₁ W + Y'))
      ≤ 2 * lam * entrySupNorm W := by
  set P := samplingProjection t₁ W with hP
  have hW' : tangentProjection S (W - q⁻¹ • P) = W - q⁻¹ • tangentProjection S P := by
    rw [g4_tp_sub, g4_tp_smul, hW]
  have hWf : frobeniusNorm (tangentProjection S (W - q⁻¹ • P)) ≤ (1 / 2) * frobeniusNorm W := by
    have h1 : tangentProjection S (W - q⁻¹ • P) = (-q⁻¹) • (tangentProjection S P - q • W) := by
      rw [hW']
      have hq' : q⁻¹ * q = 1 := inv_mul_cancel₀ hq.ne'
      rw [smul_sub, smul_smul, neg_mul, hq', neg_smul, neg_smul, one_smul]
      abel
    rw [h1, g4_frob_smul, abs_neg, abs_of_pos (inv_pos.mpr hq)]
    have := mul_le_mul_of_nonneg_left hF (inv_nonneg.mpr hq.le)
    calc q⁻¹ * frobeniusNorm (tangentProjection S P - q • W)
        ≤ q⁻¹ * ((1 / 2) * q * frobeniusNorm W) := this
      _ = (1 / 2) * frobeniusNorm W := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp only [Finset.mem_union, not_or] at hij
    simp only [Matrix.add_apply, Matrix.smul_apply, hP, samplingProjection, if_neg hij.1,
      hY'v i j hij.2, smul_eq_mul, mul_zero, add_zero]
  · have h2 : W - tangentProjection S (q⁻¹ • P + Y') =
        tangentProjection S (W - q⁻¹ • P) - tangentProjection S Y' := by
      rw [g4_tp_add, g4_tp_smul, hW']; abel
    rw [h2]
    calc _ ≤ (1 / 2) ^ k * frobeniusNorm (tangentProjection S (W - q⁻¹ • P)) := hY'f
      _ ≤ (1 / 2) ^ k * ((1 / 2) * frobeniusNorm W) :=
          mul_le_mul_of_nonneg_left hWf (by positivity)
      _ = (1 / 2) ^ (k + 1) * frobeniusNorm W := by ring
  · have hC : q⁻¹ • P = centeredSamplingFluctuation t₁ q W + W := by
      unfold centeredSamplingFluctuation
      rw [← hP, smul_sub, smul_smul, inv_mul_cancel₀ hq.ne', one_smul]; abel
    have hNW : normalProjection S W = 0 := by unfold normalProjection; rw [hW]; abel
    rw [g4_np_add, hC, g4_np_add, hNW, add_zero]
    have e0 := g4_entry_nonneg W
    calc _ ≤ spectralNorm (normalProjection S (centeredSamplingFluctuation t₁ q W))
          + spectralNorm (normalProjection S Y') := g4_spec_add _ _
      _ ≤ lam * entrySupNorm W + 2 * lam * ((1 / 2) * entrySupNorm W) := by
          gcongr
          · exact (hnorm _).trans hS
          · exact hY's.trans (mul_le_mul_of_nonneg_left hE (by positivity))
      _ = 2 * lam * entrySupNorm W := by ring

theorem g4_frob_sub_comm {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    frobeniusNorm (X - Y) = frobeniusNorm (Y - X) := by
  have h : X - Y = (-1 : ℝ) • (Y - X) := by module
  rw [h, g4_frob_smul]; simp

theorem g4_frob_eq_zero {n1 n2 : ℕ} (H : RealMatrix n1 n2) (h : frobeniusNorm H = 0) : H = 0 := by
  unfold frobeniusNorm at h
  rw [Real.sqrt_eq_zero (g4_frobSq_nonneg H)] at h
  unfold frobeniusNormSq at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h1 j (Finset.mem_univ _)
  simpa using h2

/-- Injectivity on T from a sub-sample with tangent concentration (b71ef15f supplies `hzero`). -/
theorem g4_inj {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (Ω₀ Ω : Finset (Fin n1 × Fin n2)) (hsub : Ω₀ ⊆ Ω)
    (hzero : ∀ H, tangentProjection S H = H → samplingProjection Ω₀ H = 0 → frobeniusNorm H = 0) :
    SamplingOperatorInjectiveOnT Ω S := by
  intro H hT hP
  refine g4_frob_eq_zero H (hzero H hT ?_)
  ext i j
  have := congrFun (congrFun hP i) j
  simp only [samplingProjection, Matrix.zero_apply] at this ⊢
  split_ifs with h0
  · simpa [hsub h0] using this
  · rfl

/-- G4 finish: correct the golfing certificate on a sub-sample with tangent concentration. -/
theorem g4_cert {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hidem : ∀ X, tangentProjection S (tangentProjection S X) = tangentProjection S X)
    (hnorm : ∀ X, spectralNorm (normalProjection S X) ≤ spectralNorm X)
    (q : ℝ) (hq : 0 < q) (Ω₀ Ω : Finset (Fin n1 × Fin n2)) (hsub : Ω₀ ⊆ Ω)
    (hTSC : TangentSamplingConcentration Ω₀ S q (1 / 2))
    (hsurj : TangentSamplingOperatorSurjectiveOnT Ω₀ S)
    (E Y : RealMatrix n1 n2) (hE : tangentProjection S E = E) (hYv : VanishesOutside Ω Y)
    (δ s : ℝ) (hYf : frobeniusNorm (E - tangentProjection S Y) ≤ δ)
    (hYs : spectralNorm (normalProjection S Y) ≤ s) :
    ∃ Y₁ : RealMatrix n1 n2, VanishesOutside Ω Y₁ ∧ tangentProjection S Y₁ = E ∧
      spectralNorm (normalProjection S Y₁) ≤ s + 2 * δ / q := by
  set R := E - tangentProjection S Y with hR
  have hRT : tangentProjection S R = R := by rw [hR, g4_tp_sub, hidem, hE]
  obtain ⟨Z, hZT, hZP⟩ := hsurj R hRT
  have hc := hTSC Z hZT
  rw [hZP] at hc
  have hZf : frobeniusNorm Z ≤ 2 * δ / q := by
    have h1 : frobeniusNorm (q • Z) ≤ frobeniusNorm R + frobeniusNorm (R - q • Z) := by
      have := g4_frob_add R (q • Z - R)
      rw [add_sub_cancel] at this
      rw [g4_frob_sub_comm R]; exact this
    rw [g4_frob_smul, abs_of_pos hq] at h1
    rw [le_div_iff₀ hq]
    nlinarith [g4_frob_nonneg Z]
  refine ⟨Y + samplingProjection Ω₀ Z, ?_, ?_, ?_⟩
  · intro i j hij
    have h0 : (i, j) ∉ Ω₀ := fun h => hij (hsub h)
    simp [samplingProjection, h0, hYv i j hij]
  · rw [g4_tp_add, hZP, hR]; abel
  · rw [g4_np_add]
    calc _ ≤ spectralNorm (normalProjection S Y)
          + spectralNorm (normalProjection S (samplingProjection Ω₀ Z)) := g4_spec_add _ _
      _ ≤ s + 2 * δ / q := by
          gcongr
          exact (hnorm _).trans ((g4_spec_le_frob _).trans ((g4_frob_samp_le _ _).trans hZf))

/-! ## from fc5b8bdf_g2.lean -/
theorem g2_weight_nonneg {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ω : Finset (Fin n1 × Fin n2)) : 0 ≤ bernoulliObservationWeight p Ω := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem g2_mono {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : Finset (Fin n1 × Fin n2) → Prop) (h : ∀ t, E t → F t) :
    bernoulliEventProb p E ≤ bernoulliEventProb p F := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum (fun t _ => ?_)
  by_cases hE : E t
  · simp [hE, h t hE]
  · by_cases hF : F t
    · simp [hE, hF, g2_weight_nonneg p hp0 hp1 t]
    · simp [hE, hF]

theorem g2_union {n1 n2 : ℕ} {ι : Type*} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset ι)
    (E : ι → Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliEventProb p (fun t => ∃ i ∈ s, E i t) ≤ ∑ i ∈ s, bernoulliEventProb p (E i) := by
  unfold bernoulliEventProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hnn : ∀ j ∈ s, 0 ≤ (if E j t then bernoulliObservationWeight p t else 0) := by
    intro j _
    split_ifs
    · exact g2_weight_nonneg p hp0 hp1 t
    · exact le_refl 0
  split_ifs with h
  · obtain ⟨i, hi, hEi⟩ := h
    have hle := Finset.single_le_sum
      (f := fun j => if E j t then bernoulliObservationWeight p t else 0) hnn hi
    simpa [hEi] using hle
  · exact Finset.sum_nonneg hnn

theorem g2_inner_coord {n1 n2 : ℕ} (X : RealMatrix n1 n2) (a : Fin n1) (b : Fin n2) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [hi]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Hadamard product `W ∘ P_T e_ab`. -/
noncomputable def g2B {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (W : RealMatrix n1 n2)
    (a : Fin n1) (b : Fin n2) : RealMatrix n1 n2 :=
  fun i j => W i j * tangentProjection S (coordinateMatrix a b) i j

theorem g2_samp_apply {n1 n2 : ℕ} (Ω : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    samplingProjection Ω X i j = if (i, j) ∈ Ω then X i j else 0 := rfl

theorem g2_cf_apply {n1 n2 : ℕ} (Ω : Finset (Fin n1 × Fin n2)) (q : ℝ) (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    centeredSamplingFluctuation Ω q X i j = q⁻¹ * ((if (i, j) ∈ Ω then X i j else 0) - q * X i j) :=
  rfl

theorem g2_entry_identity {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hsa : ∀ A B : RealMatrix n1 n2,
      matrixInner (tangentProjection S A) B = matrixInner A (tangentProjection S B))
    (q : ℝ) (hq : q ≠ 0) (Ω : Finset (Fin n1 × Fin n2)) (W : RealMatrix n1 n2)
    (a : Fin n1) (b : Fin n2) :
    tangentProjection S (W - q⁻¹ • samplingProjection Ω W) a b =
      - matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W a b)) := by
  rw [← g2_inner_coord (tangentProjection S _) a b, hsa]
  unfold matrixInner matrixEntrySum
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, g2_samp_apply, g2_cf_apply, g2B]
  by_cases h : (i, j) ∈ Ω <;> simp only [h, if_true, if_false] <;> field_simp <;> ring

theorem g2_abs_le_sup {n1 n2 : ℕ} (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j, |X i j|) (Set.finite_range _).bddAbove i)
  exact le_ciSup (f := fun j => |X i j|) (Set.finite_range _).bddAbove j

theorem g2_entry_nonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

/-- G2: entry-wise contraction of one golfing batch, via the scalar Bernstein tail (270d8ab7,
supplied as `hBern`) and a union bound over the `n1 * n2` entries. -/
theorem g2_entry_bound {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hsa : ∀ A B : RealMatrix n1 n2,
      matrixInner (tangentProjection S A) B = matrixInner A (tangentProjection S B))
    (hBern : ∀ (p u : ℝ) (X : RealMatrix n1 n2), 0 < p → p ≤ 1 → 0 ≤ u →
      0 < frobeniusNormSq X →
      bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|) ≤ 2 * Real.exp (-u))
    (κ q u : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hκ1 : ∀ a b, frobeniusNormSq (tangentProjection S (coordinateMatrix a b)) ≤ κ)
    (hκ2 : ∀ a b i j, |tangentProjection S (coordinateMatrix a b) i j| ≤ κ)
    (hcond : Real.sqrt (2 * (κ / q) * u) + (2 / 3) * (κ / q) * u ≤ 1 / 2)
    (W : RealMatrix n1 n2) :
    bernoulliEventProb q (fun Ω => ¬ entrySupNorm
        (tangentProjection S (W - q⁻¹ • samplingProjection Ω W)) ≤ (1 / 2) * entrySupNorm W)
      ≤ ((n1 : ℝ) * n2) * (2 * Real.exp (-u)) := by
  have hw0 : 0 ≤ entrySupNorm W := g2_entry_nonneg W
  have hhalf : 0 ≤ (1 / 2) * entrySupNorm W := mul_nonneg (by norm_num) hw0
  have hsub : ∀ Ω : Finset (Fin n1 × Fin n2),
      ¬ entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection Ω W))
          ≤ (1 / 2) * entrySupNorm W →
      ∃ ab ∈ (Finset.univ : Finset (Fin n1 × Fin n2)), (1 / 2) * entrySupNorm W
        < |matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W ab.1 ab.2))| := by
    intro Ω h
    by_contra hne
    push Not at hne
    apply h
    unfold entrySupNorm
    refine Real.iSup_le (fun a => Real.iSup_le (fun b => ?_) hhalf) hhalf
    rw [g2_entry_identity S hsa q hq0.ne' Ω W a b, abs_neg]
    exact hne (a, b) (Finset.mem_univ _)
  have hE : ∀ ab : Fin n1 × Fin n2, bernoulliEventProb q (fun Ω => (1 / 2) * entrySupNorm W
        < |matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W ab.1 ab.2))|)
        ≤ 2 * Real.exp (-u) := by
    rintro ⟨a, b⟩
    have hBf : frobeniusNormSq (g2B S W a b) ≤ entrySupNorm W ^ 2 * κ := by
      calc frobeniusNormSq (g2B S W a b)
          ≤ ∑ i, ∑ j, entrySupNorm W ^ 2 * (tangentProjection S (coordinateMatrix a b) i j) ^ 2 := by
            unfold frobeniusNormSq
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
            simp only [g2B]
            rw [mul_pow]
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (g2_abs_le_sup W i j) 2
        _ = entrySupNorm W ^ 2 * frobeniusNormSq (tangentProjection S (coordinateMatrix a b)) := by
            unfold frobeniusNormSq; rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ entrySupNorm W ^ 2 * κ := mul_le_mul_of_nonneg_left (hκ1 a b) (sq_nonneg _)
    have hBs : entrySupNorm (g2B S W a b) ≤ entrySupNorm W * κ := by
      have h0 : 0 ≤ entrySupNorm W * κ := mul_nonneg hw0 hκ
      unfold entrySupNorm
      refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) h0) h0
      simp only [g2B]
      rw [abs_mul]
      exact mul_le_mul (g2_abs_le_sup W i j) (hκ2 a b i j) (abs_nonneg _) hw0
    by_cases hpos : 0 < frobeniusNormSq (g2B S W a b)
    · refine le_trans (g2_mono q hq0.le hq1 _ _ (fun Ω hΩ => ?_))
        (hBern q u (g2B S W a b) hq0 hq1 hu hpos)
      refine lt_of_le_of_lt ?_ hΩ
      have h1 : frobeniusNormSq (g2B S W a b) / q ≤ entrySupNorm W ^ 2 * κ / q :=
        div_le_div_of_nonneg_right hBf hq0.le
      have h2 : entrySupNorm (g2B S W a b) / q ≤ entrySupNorm W * κ / q :=
        div_le_div_of_nonneg_right hBs hq0.le
      calc Real.sqrt (2 * (frobeniusNormSq (g2B S W a b) / q) * u)
            + 2 / 3 * (entrySupNorm (g2B S W a b) / q) * u
          ≤ Real.sqrt (2 * (entrySupNorm W ^ 2 * κ / q) * u)
            + 2 / 3 * (entrySupNorm W * κ / q) * u :=
            add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (by norm_num)) hu))
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hu)
        _ = entrySupNorm W * (Real.sqrt (2 * (κ / q) * u) + (2 / 3) * (κ / q) * u) := by
            rw [show 2 * (entrySupNorm W ^ 2 * κ / q) * u
                = entrySupNorm W ^ 2 * (2 * (κ / q) * u) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw0]
            ring
        _ ≤ entrySupNorm W * (1 / 2) := mul_le_mul_of_nonneg_left hcond hw0
        _ = 1 / 2 * entrySupNorm W := by ring
    · have h0 : frobeniusNormSq (g2B S W a b) = 0 :=
        le_antisymm (not_lt.mp hpos) (by unfold frobeniusNormSq; positivity)
      have hB0 : ∀ i j, g2B S W a b i j = 0 := by
        intro i j
        unfold frobeniusNormSq at h0
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h0 i
          (Finset.mem_univ _)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h1 j
          (Finset.mem_univ _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      have hz : bernoulliEventProb q (fun Ω => (1 / 2) * entrySupNorm W
          < |matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W a b))|) = 0 := by
        unfold bernoulliEventProb
        refine Finset.sum_eq_zero (fun Ω _ => ?_)
        rw [if_neg]
        intro hΩ
        have hzz : matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W a b)) = 0 := by
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          simp only [g2_cf_apply, hB0]
          simp
        rw [hzz, abs_zero] at hΩ
        linarith
      simp only at hz ⊢
      rw [hz]; positivity
  calc bernoulliEventProb q (fun Ω => ¬ entrySupNorm
        (tangentProjection S (W - q⁻¹ • samplingProjection Ω W)) ≤ (1 / 2) * entrySupNorm W)
      ≤ bernoulliEventProb q (fun Ω => ∃ ab ∈ (Finset.univ : Finset (Fin n1 × Fin n2)),
          (fun (ab : Fin n1 × Fin n2) Ω => (1 / 2) * entrySupNorm W
            < |matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W ab.1 ab.2))|) ab Ω) :=
        g2_mono q hq0.le hq1 _ _ hsub
    _ ≤ ∑ ab ∈ (Finset.univ : Finset (Fin n1 × Fin n2)), bernoulliEventProb q
          ((fun (ab : Fin n1 × Fin n2) Ω => (1 / 2) * entrySupNorm W
            < |matrixEntrySum (centeredSamplingFluctuation Ω q (g2B S W ab.1 ab.2))|) ab) :=
        g2_union q hq0.le hq1 _ _
    _ ≤ ∑ ab ∈ (Finset.univ : Finset (Fin n1 × Fin n2)), 2 * Real.exp (-u) :=
        Finset.sum_le_sum (fun ab _ => hE ab)
    _ = ((n1 : ℝ) * n2) * (2 * Real.exp (-u)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring

/-! ## from fc5b8bdf_g5.lean -/
theorem g5_tp_coord_apply {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (a i : Fin n1) (b j : Fin n2) :
    tangentProjection S (coordinateMatrix a b) i j =
      (∑ k, S.u k i * S.u k a) * (if j = b then 1 else 0)
        + (if i = a then 1 else 0) * (∑ k, S.v k b * S.v k j)
        - (∑ k, S.u k i * S.u k a) * (∑ k, S.v k b * S.v k j) := by
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, coordinateMatrix, Matrix.add_apply, Matrix.sub_apply]
  congr 1
  · congr 1
    · rw [Finset.sum_eq_single a]
      · simp
      · intro x _ hx; simp [hx]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [Finset.sum_eq_single b]
      · simp
      · intro x _ hx; simp [hx]
      · intro h; exact absurd (Finset.mem_univ b) h
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro x _ hx; simp [hx]
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro x _ hx
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [hx]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem g5_tp_coord_abs {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ i a : Fin n1, |∑ k, S.u k i * S.u k a| ≤ ρ)
    (hV : ∀ b j : Fin n2, |∑ k, S.v k b * S.v k j| ≤ ρ)
    (a i : Fin n1) (b j : Fin n2) :
    |tangentProjection S (coordinateMatrix a b) i j| ≤ 2 * ρ + ρ ^ 2 := by
  rw [g5_tp_coord_apply]
  have h1 : |(∑ k, S.u k i * S.u k a) * (if j = b then (1:ℝ) else 0)| ≤ ρ := by
    rw [abs_mul]
    have : |(if j = b then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc _ ≤ ρ * 1 := mul_le_mul (hU i a) this (abs_nonneg _) hρ
      _ = ρ := mul_one ρ
  have h2 : |(if i = a then (1:ℝ) else 0) * (∑ k, S.v k b * S.v k j)| ≤ ρ := by
    rw [abs_mul]
    have : |(if i = a then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc _ ≤ 1 * ρ := mul_le_mul this (hV b j) (abs_nonneg _) zero_le_one
      _ = ρ := one_mul ρ
  have h3 : |(∑ k, S.u k i * S.u k a) * (∑ k, S.v k b * S.v k j)| ≤ ρ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (hU i a) (hV b j) (abs_nonneg _) hρ
  calc _ ≤ |(∑ k, S.u k i * S.u k a) * (if j = b then (1:ℝ) else 0)
        + (if i = a then (1:ℝ) else 0) * (∑ k, S.v k b * S.v k j)|
        + |(∑ k, S.u k i * S.u k a) * (∑ k, S.v k b * S.v k j)| := abs_sub _ _
    _ ≤ (|(∑ k, S.u k i * S.u k a) * (if j = b then (1:ℝ) else 0)|
        + |(if i = a then (1:ℝ) else 0) * (∑ k, S.v k b * S.v k j)|)
        + |(∑ k, S.u k i * S.u k a) * (∑ k, S.v k b * S.v k j)| := by
          gcongr; exact abs_add_le _ _
    _ ≤ (ρ + ρ) + ρ ^ 2 := by gcongr
    _ = 2 * ρ + ρ ^ 2 := by ring

theorem g5_frobSq_tp_coord {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hsa : ∀ A B : RealMatrix n1 n2,
      matrixInner (tangentProjection S A) B = matrixInner A (tangentProjection S B))
    (hidem : ∀ X, tangentProjection S (tangentProjection S X) = tangentProjection S X)
    (a : Fin n1) (b : Fin n2) :
    frobeniusNormSq (tangentProjection S (coordinateMatrix a b))
      = tangentProjection S (coordinateMatrix a b) a b := by
  have h1 : frobeniusNormSq (tangentProjection S (coordinateMatrix a b)) =
      matrixInner (tangentProjection S (coordinateMatrix a b))
        (tangentProjection S (coordinateMatrix a b)) := by
    unfold frobeniusNormSq matrixInner
    simp only [sq]
  rw [h1, ← hsa, hidem]
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [hi]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem g5_rho {N r : ℕ} (u : Fin r → (Fin N → ℝ)) (μ : ℝ) (h : CandesTao.Shared.ProjectionIncoherent u μ)
    (a a' : Fin N) :
    |∑ k, u k a * u k a'| ≤ (r : ℝ) / N + μ * Real.sqrt r / N := by
  have h1 := h a a'
  have h2 : |(if a = a' then (r : ℝ) / (N : ℝ) else 0)| ≤ (r : ℝ) / N := by
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
    · simp; positivity
  calc |∑ k, u k a * u k a'|
      = |((∑ k, u k a * u k a') - (if a = a' then (r : ℝ) / (N : ℝ) else 0))
          + (if a = a' then (r : ℝ) / (N : ℝ) else 0)| := by ring_nf
    _ ≤ |(∑ k, u k a * u k a') - (if a = a' then (r : ℝ) / (N : ℝ) else 0)|
          + |(if a = a' then (r : ℝ) / (N : ℝ) else 0)| := abs_add_le _ _
    _ ≤ μ * Real.sqrt r / N + (r : ℝ) / N := add_le_add h1 h2
    _ = (r : ℝ) / N + μ * Real.sqrt r / N := by ring

/-! ## Core: golfing => unique recovery, Bernoulli failure bound -/

theorem g6_tp_zero {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) :
    tangentProjection S 0 = 0 := by
  have h := g4_tp_smul S 0 0
  simpa using h

theorem g6_spec_zero {n1 n2 : ℕ} : MatrixCompletion.spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  unfold MatrixCompletion.spectralNorm
  rw [map_zero, map_zero, norm_zero]

theorem golf_core {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (hidem : ∀ X, tangentProjection S (tangentProjection S X) = tangentProjection S X)
    (hnorm : ∀ X, spectralNorm (normalProjection S X) ≤ spectralNorm X)
    (q lam ε : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam) (K : ℕ) (hK : K ≠ 0)
    (hsurjF : ∀ Ω : Finset (Fin n1 × Fin n2), TangentSamplingConcentration Ω S q (1 / 2) →
      TangentSamplingOperatorSurjectiveOnT Ω S)
    (hzeroF : ∀ (Ω : Finset (Fin n1 × Fin n2)) (H : RealMatrix n1 n2),
      TangentSamplingConcentration Ω S q (1 / 2) →
      tangentProjection S H = H → samplingProjection Ω H = 0 → frobeniusNorm H = 0)
    (hcertF : ∀ Ω : Finset (Fin n1 × Fin n2), SamplingOperatorInjectiveOnT Ω S →
      (∃ Y, StrictDualCertificate Ω S Y) → IsUniqueMinimizer Ω M)
    (hTE : tangentProjection S (signMatrix S) = signMatrix S)
    (heps : ∀ W : RealMatrix n1 n2, tangentProjection S W = W →
      bernoulliEventProb q (fun t => ¬ (TangentSamplingConcentration t S q (1 / 2) ∧
        entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t W))
          ≤ (1 / 2) * entrySupNorm W ∧
        spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W)) ≤ ε)
    (hnum : 2 * lam * entrySupNorm (signMatrix S)
      + 2 * ((1 / 2) ^ K * frobeniusNorm (signMatrix S)) / q < 1) :
    bernoulliEventProb (1 - (1 - q) ^ K) (fun t => ¬ IsUniqueMinimizer t M) ≤ K * ε := by
  have hrec := golf_rec_prob (n₁ := n1) (n₂ := n2) (σ := RealMatrix n1 n2) q ε hq0.le hq1
    (fun W => tangentProjection S W = W)
    (fun t W => tangentProjection S (W - q⁻¹ • samplingProjection t W))
    (fun t W => TangentSamplingConcentration t S q (1 / 2) ∧
        entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t W))
          ≤ (1 / 2) * entrySupNorm W ∧
        spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W)
    (fun k t W => ∃ Y : RealMatrix n1 n2, VanishesOutside t Y ∧
        frobeniusNorm (W - tangentProjection S Y) ≤ (1 / 2) ^ k * frobeniusNorm W ∧
        spectralNorm (normalProjection S Y) ≤ 2 * lam * entrySupNorm W ∧
        (k ≠ 0 → ∃ t₀ ⊆ t, TangentSamplingConcentration t₀ S q (1 / 2)))
    (fun t W _ => hidem _)
    (by
      intro t W _
      refine ⟨0, fun _ _ _ => rfl, ?_, ?_, fun h => absurd rfl h⟩
      · rw [g6_tp_zero, sub_zero, pow_zero, one_mul]
      · have : normalProjection S (0 : RealMatrix n1 n2) = 0 := by
          unfold normalProjection; rw [g6_tp_zero, sub_zero]
        rw [this, g6_spec_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hlam) (g2_entry_nonneg W))
    (by
      intro k t₁ t₂ W hW hG hR
      obtain ⟨hTSC, hE, hS⟩ := hG
      obtain ⟨Y', hv, hf, hs, _⟩ := hR
      have h := g4_step S hnorm q lam hq0 hlam k t₁ t₂ W hW (hTSC W hW) hE hS Y' hv hf hs
      exact ⟨_, h.1, h.2.1, h.2.2, fun _ => ⟨t₁, Finset.subset_union_left, hTSC⟩⟩)
    heps
  have hq' : 0 ≤ 1 - (1 - q) ^ K := by
    have : (1 - q) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hq'' : 1 - (1 - q) ^ K ≤ 1 := by
    have : 0 ≤ (1 - q) ^ K := pow_nonneg (by linarith) K
    linarith
  have h2 := hrec K (signMatrix S) hTE
  refine le_trans ?_ h2
  apply g2_mono _ hq' hq''
  intro t ht hR
  apply ht
  obtain ⟨Y, hv, hf, hs, ht0⟩ := hR
  obtain ⟨t₀, hsub, hTSC⟩ := ht0 hK
  obtain ⟨Y₁, hv1, hT1, hs1⟩ := g4_cert S hidem hnorm q hq0 t₀ t hsub hTSC (hsurjF t₀ hTSC)
    (signMatrix S) Y hTE hv _ _ hf hs
  refine hcertF t (g4_inj S t₀ t hsub (fun H hH hP => hzeroF t₀ H hTSC hH hP)) ⟨Y₁, hv1, hT1, ?_⟩
  exact lt_of_le_of_lt hs1 hnum

theorem g3_and {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliEventProb p (fun t => ¬ (A t ∧ B t))
      ≤ bernoulliEventProb p (fun t => ¬ A t) + bernoulliEventProb p (fun t => ¬ B t) := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hw := g2_weight_nonneg p hp0 hp1 t
  by_cases hA : A t <;> by_cases hB : B t <;> simp [hA, hB, hw]

/-- G3: per-batch failure of the golfing `Good` event is the sum of the three tails. -/
theorem g3_eps {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (q lam a b e : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (W : RealMatrix n1 n2)
    (hA : bernoulliEventProb q (fun t => ¬ TangentSamplingConcentration t S q (1 / 2)) ≤ a)
    (hE : bernoulliEventProb q (fun t => ¬ entrySupNorm
        (tangentProjection S (W - q⁻¹ • samplingProjection t W)) ≤ (1 / 2) * entrySupNorm W) ≤ e)
    (hB : bernoulliEventProb q (fun t =>
        ¬ spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W) ≤ b) :
    bernoulliEventProb q (fun t => ¬ (TangentSamplingConcentration t S q (1 / 2) ∧
        entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t W))
          ≤ (1 / 2) * entrySupNorm W ∧
        spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W)) ≤ a + e + b := by
  refine le_trans (g3_and q hq0 hq1 _ _) ?_
  have h2 := g3_and q hq0 hq1
    (fun t => entrySupNorm (tangentProjection S (W - q⁻¹ • samplingProjection t W))
          ≤ (1 / 2) * entrySupNorm W)
    (fun t => spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W)
  linarith

/-! ## square-case projection algebra (copied from scratch/probe/38087c24_g26t.lean) -/

namespace FCRP

/-! ## Projection algebra (copied from scratch/decomp/429b6866 and 0363db4b) -/

noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma orth_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    projM u * projM u = projM u := by
  ext i c
  simp only [Matrix.mul_apply, projM]
  have h1 : ∀ a, (∑ k, u k i * u k a) * (∑ l, u l a * u l c) =
      ∑ k, ∑ l, u k i * u l c * (u k a * u l a) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ a, u k i * u l c * (u k a * u l a) =
      u k i * u l c * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hu]
  simp_rw [h2]
  simp

lemma PU_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PU SV * PU SV = PU SV :=
  orth_idem SV.u SV.u_orthonormal

lemma PV_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PV SV * PV SV = PV SV :=
  orth_idem SV.v SV.v_orthonormal

lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma tangent_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X + Y) = tangentProjection SV X + tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul]
  abel

lemma tangent_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X - Y) = tangentProjection SV X - tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma tangent_smul {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : ℝ) (X : RealMatrix n n) :
    tangentProjection SV (c • X) = c • tangentProjection SV X := by
  simp only [tangent_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

lemma tangent_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (tangentProjection SV X) = tangentProjection SV X := by
  have hA := PU_idem SV
  have hB := PV_idem SV
  have hB' : ∀ Y : RealMatrix n n, Y * PV SV * PV SV = Y * PV SV := by
    intro Y; rw [Matrix.mul_assoc, hB]
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, hA, hB']
  abel

lemma projM_mul_vmv {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    projM u * Matrix.vecMulVec (u k) w = Matrix.vecMulVec (u k) w := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ a, (∑ l, u l i * u l a) * (u k a * w j) = ∑ l, u l i * w j * (u l a * u k a) := by
    intro a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hu]
  simp

lemma vmv_mul_projM {n r : ℕ} (v : Fin r → Fin n → ℝ)
    (hv : ∀ k l, ∑ i, v k i * v l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    Matrix.vecMulVec w (v k) * projM v = Matrix.vecMulVec w (v k) := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ b, w i * v k b * (∑ l, v l b * v l j) = ∑ l, w i * v l j * (v k b * v l b) := by
    intro b
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hv]
  simp

lemma PU_mul_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    PU SV * signMatrix SV = signMatrix SV := by
  unfold signMatrix PU
  rw [Matrix.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => projM_mul_vmv SV.u SV.u_orthonormal k (SV.v k))

lemma sign_mul_PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    signMatrix SV * PV SV = signMatrix SV := by
  unfold signMatrix PV
  rw [Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => vmv_mul_projM SV.v SV.v_orthonormal k (SV.u k))

lemma tangent_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    tangentProjection SV (signMatrix SV) = signMatrix SV := by
  rw [tangent_eq, PU_mul_sign, sign_mul_PV]
  abel

lemma normal_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    normalProjection SV X = (1 - PU SV) * X * (1 - PV SV) := by
  simp only [normalProjection, tangent_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one]
  abel

lemma normal_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    normalProjection SV (X + Y) = normalProjection SV X + normalProjection SV Y := by
  simp only [normalProjection, tangent_add]
  abel

lemma normal_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    normalProjection SV (X - Y) = normalProjection SV X - normalProjection SV Y := by
  simp only [normalProjection, tangent_sub]
  abel

/-! ## Norm facts -/

open scoped Matrix.Norms.L2Operator in
lemma spec_eq {n : ℕ} (X : RealMatrix n n) : MatrixCompletion.spectralNorm X = ‖X‖ := rfl

open scoped Matrix.Norms.L2Operator in
lemma proj_norm_le {n : ℕ} (P : RealMatrix n n) (hP : P * P = P)
    (hT : Matrix.transpose P = P) : ‖(1 - P : RealMatrix n n)‖ ≤ 1 := by
  have hQ : (1 - P : RealMatrix n n) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hP]
    abel
  have hH : Matrix.conjTranspose (1 - P : RealMatrix n n) = 1 - P := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, hT]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (1 - P : RealMatrix n n)
  rw [hH, hQ] at h
  have h0 : 0 ≤ ‖(1 - P : RealMatrix n n)‖ := norm_nonneg _
  nlinarith

open scoped Matrix.Norms.L2Operator in
lemma spectral_normal_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    MatrixCompletion.spectralNorm (normalProjection SV X) ≤ MatrixCompletion.spectralNorm X := by
  rw [spec_eq, spec_eq, normal_eq]
  have hU := proj_norm_le (PU SV) (PU_idem SV) (projM_transpose SV.u)
  have hV := proj_norm_le (PV SV) (PV_idem SV) (projM_transpose SV.v)
  calc ‖(1 - PU SV) * X * (1 - PV SV)‖ ≤ ‖(1 - PU SV) * X‖ * ‖(1 - PV SV)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(1 - PU SV)‖ * ‖X‖) * ‖(1 - PV SV)‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
        apply mul_le_mul _ hV (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hU (norm_nonneg _)
    _ = ‖X‖ := by ring

end FCRP

/-! ## self-adjointness (square case) and the TSC kernel fact, proved locally -/

theorem g7_mi_trace {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = Matrix.trace (Matrix.transpose X * Y) := by
  unfold matrixInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem g7_hsa {n r : ℕ} {M : RealMatrix n n} (S : SVD M r) (A B : RealMatrix n n) :
    matrixInner (tangentProjection S A) B = matrixInner A (tangentProjection S B) := by
  rw [g7_mi_trace, g7_mi_trace, FCRP.tangent_eq, FCRP.tangent_eq]
  have hU : Matrix.transpose (FCRP.PU S) = FCRP.PU S := FCRP.projM_transpose S.u
  have hV : Matrix.transpose (FCRP.PV S) = FCRP.PV S := FCRP.projM_transpose S.v
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul, hU, hV,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add,
    Matrix.trace_sub, Matrix.mul_assoc]
  have h1 : Matrix.trace (FCRP.PV S * (Matrix.transpose A * B))
      = Matrix.trace (Matrix.transpose A * (B * FCRP.PV S)) := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : Matrix.trace (FCRP.PV S * (Matrix.transpose A * (FCRP.PU S * B)))
      = Matrix.trace (Matrix.transpose A * (FCRP.PU S * (B * FCRP.PV S))) := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h1, h2]

theorem g7_hzero {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (q : ℝ) (hq : 0 < q)
    (Ω : Finset (Fin n1 × Fin n2)) (H : RealMatrix n1 n2)
    (hT : TangentSamplingConcentration Ω S q (1 / 2))
    (hH : tangentProjection S H = H) (hP : samplingProjection Ω H = 0) :
    frobeniusNorm H = 0 := by
  have h := hT H hH
  rw [hP, g6_tp_zero, zero_sub] at h
  have h2 : frobeniusNorm (-(q • H)) = q * frobeniusNorm H := by
    rw [show -(q • H) = (-q) • H by rw [neg_smul], g4_frob_smul, abs_neg, abs_of_pos hq]
  rw [h2] at h
  have h0 := g4_frob_nonneg H
  nlinarith

/-! ## Square case: golf_core with every structural fact discharged; only probabilistic tails and
numerics remain as hypotheses. -/

theorem golf_square {n r : ℕ} {M : RealMatrix n n} (S : SVD M r) (μ : ℝ)
    (hSI : CandesTao.Shared.StrongIncoherence S μ)
    (q lam a b u ρ : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam) (K : ℕ) (hK : K ≠ 0)
    (hu : 0 ≤ u) (hρ0 : 0 ≤ ρ) (hρ : (r : ℝ) / n + μ * Real.sqrt r / n ≤ ρ)
    (hsurjF : ∀ Ω : Finset (Fin n × Fin n), TangentSamplingConcentration Ω S q (1 / 2) →
      TangentSamplingOperatorSurjectiveOnT Ω S)
    (hcertF : ∀ Ω : Finset (Fin n × Fin n), SamplingOperatorInjectiveOnT Ω S →
      (∃ Y, StrictDualCertificate Ω S Y) → IsUniqueMinimizer Ω M)
    (hBern : ∀ (p u : ℝ) (X : RealMatrix n n), 0 < p → p ≤ 1 → 0 ≤ u →
      0 < frobeniusNormSq X →
      bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|) ≤ 2 * Real.exp (-u))
    (hcond : Real.sqrt (2 * ((2 * ρ + ρ ^ 2) / q) * u) + (2 / 3) * ((2 * ρ + ρ ^ 2) / q) * u
      ≤ 1 / 2)
    (hA : bernoulliEventProb q (fun t => ¬ TangentSamplingConcentration t S q (1 / 2)) ≤ a)
    (hB : ∀ W : RealMatrix n n, bernoulliEventProb q (fun t =>
        ¬ spectralNorm (centeredSamplingFluctuation t q W) ≤ lam * entrySupNorm W) ≤ b)
    (hnum : 2 * lam * entrySupNorm (signMatrix S)
      + 2 * ((1 / 2) ^ K * frobeniusNorm (signMatrix S)) / q < 1) :
    bernoulliEventProb (1 - (1 - q) ^ K) (fun t => ¬ IsUniqueMinimizer t M)
      ≤ K * (a + ((n : ℝ) * n) * (2 * Real.exp (-u)) + b) := by
  have hU : ∀ i a' : Fin n, |∑ k, S.u k i * S.u k a'| ≤ ρ :=
    fun i a' => (g5_rho S.u μ hSI.2.1 i a').trans hρ
  have hV : ∀ b' j : Fin n, |∑ k, S.v k b' * S.v k j| ≤ ρ :=
    fun b' j => (g5_rho S.v μ hSI.2.2.1 b' j).trans hρ
  have hκ2 : ∀ (a' : Fin n) (b' : Fin n) (i : Fin n) (j : Fin n),
      |tangentProjection S (coordinateMatrix a' b') i j| ≤ 2 * ρ + ρ ^ 2 :=
    fun a' b' i j => g5_tp_coord_abs S ρ hρ0 hU hV a' i b' j
  have hκ1 : ∀ (a' : Fin n) (b' : Fin n),
      frobeniusNormSq (tangentProjection S (coordinateMatrix a' b')) ≤ 2 * ρ + ρ ^ 2 := by
    intro a' b'
    rw [g5_frobSq_tp_coord S (g7_hsa S) (FCRP.tangent_idem S) a' b']
    exact (le_abs_self _).trans (hκ2 a' b' a' b')
  have hκ : 0 ≤ 2 * ρ + ρ ^ 2 := add_nonneg (mul_nonneg (by norm_num) hρ0) (sq_nonneg ρ)
  exact golf_core S (FCRP.tangent_idem S) (FCRP.spectral_normal_le S) q lam _ hq0 hq1 hlam K hK
    hsurjF (fun Ω H hT hH hP => g7_hzero S q hq0 Ω H hT hH hP) hcertF (FCRP.tangent_sign S)
    (fun W _ => g3_eps S q lam a b _ hq0.le hq1 W hA
      (g2_entry_bound S (g7_hsa S) hBern (2 * ρ + ρ ^ 2) q u hq0 hq1 hu hκ hκ1 hκ2 hcond W)
      (hB W)) hnum

/-! ## G5/G6 numerics (relay 3) -/

theorem fin_all_good {n1 n2 : ℕ} (m : ℕ) (M : RealMatrix n1 n2)
    (h : ∀ Ω : Finset (Fin n1 × Fin n2), IsUniqueMinimizer Ω M) (hm : m ≤ n1 * n2) :
    successProb m M = 1 := by
  unfold successProb
  dsimp only
  rw [Finset.filter_true_of_mem (fun Ω _ => h Ω)]
  have hpos : 0 < (Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    exact Nat.choose_pos hm
  have : ((Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))).card : ℝ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact div_self this

theorem fin_tp_r0 {n1 n2 : ℕ} {M : RealMatrix n1 n2} (S : SVD M 0) (X : RealMatrix n1 n2) :
    tangentProjection S X = 0 := by
  unfold tangentProjection
  ext i j
  simp [leftSingularProjection, rightSingularProjection, twoSidedSingularProjection]

theorem fin_sign_r0 {n1 n2 : ℕ} {M : RealMatrix n1 n2} (S : SVD M 0) : signMatrix S = 0 := by
  simp [signMatrix]

theorem fin_r0_good {n1 n2 : ℕ} {M : RealMatrix n1 n2} (S : SVD M 0)
    (hcert : ∀ Ω : Finset (Fin n1 × Fin n2), SamplingOperatorInjectiveOnT Ω S →
      (∃ Y, StrictDualCertificate Ω S Y) → IsUniqueMinimizer Ω M)
    (Ω : Finset (Fin n1 × Fin n2)) : IsUniqueMinimizer Ω M := by
  apply hcert Ω
  · intro H hT _
    rw [← hT, fin_tp_r0]
  · refine ⟨0, fun _ _ _ => rfl, ?_, ?_⟩
    · rw [fin_tp_r0, fin_sign_r0]
    · unfold normalProjection
      rw [fin_tp_r0, sub_zero, g6_spec_zero]
      norm_num

theorem fin_entry_le {n1 n2 : ℕ} (X : RealMatrix n1 n2) (B : ℝ) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (h : ∀ i j, |X i j| ≤ B) : entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n1) := ⟨⟨0, hn1⟩⟩
  haveI : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
  exact ciSup_le fun i => ciSup_le fun j => h i j

theorem fin_frobSq_le {n1 n2 : ℕ} (X : RealMatrix n1 n2) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) : frobeniusNormSq X ≤ (n1 : ℝ) * n2 * B ^ 2 := by
  unfold frobeniusNormSq
  calc ∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2 ≤ ∑ _i : Fin n1, ∑ _j : Fin n2, B ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          sq_le_sq' (abs_le.mp (h i j)).1 (abs_le.mp (h i j)).2
    _ = (n1 : ℝ) * n2 * B ^ 2 := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem fin_coh {N r : ℕ} (u : Fin r → Fin N → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (h : CandesTao.Shared.ProjectionIncoherent u μ) (hN : 0 < N) (hr : 0 < r) :
    coherence N r u ≤ 1 + μ := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hrr : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hsup : (⨆ i : Fin N, ∑ k, (u k i) ^ 2) ≤ (r : ℝ) / N + μ * Real.sqrt r / N := by
    refine ciSup_le fun i => ?_
    have := g5_rho u μ h i i
    calc ∑ k, (u k i) ^ 2 = ∑ k, u k i * u k i := by simp [sq]
      _ ≤ |∑ k, u k i * u k i| := le_abs_self _
      _ ≤ _ := this
  have hsq : Real.sqrt r ≤ r := by
    calc Real.sqrt r ≤ Real.sqrt ((r:ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = r := Real.sqrt_sq (by linarith)
  unfold coherence
  calc (N : ℝ) / r * ⨆ i : Fin N, ∑ k, (u k i) ^ 2
      ≤ (N : ℝ) / r * ((r : ℝ) / N + μ * Real.sqrt r / N) :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = 1 + μ * (Real.sqrt r / r) := by field_simp
    _ ≤ 1 + μ * 1 := by
        gcongr
        rw [div_le_one (by linarith)]; exact hsq
    _ = 1 + μ := by ring

theorem fin_log2 (n : ℕ) (hn : 0 < n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h1 : (2:ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have h2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
  have h3 := Real.log_two_gt_d9
  have h4 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

theorem fin_pow (n : ℕ) : 4 * n ^ 3 ≤ 2 ^ (3 * Nat.log 2 n + 5) := by
  have h : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h3 : n ^ 3 ≤ (2 ^ (Nat.log 2 n + 1)) ^ 3 := Nat.pow_le_pow_left h.le 3
  calc 4 * n ^ 3 ≤ 4 * (2 ^ (Nat.log 2 n + 1)) ^ 3 := Nat.mul_le_mul_left 4 h3
    _ = 2 ^ (3 * Nat.log 2 n + 5) := by ring

theorem fin_cond (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 16) :
    Real.sqrt (2 * x) + (2 / 3) * x ≤ 1 / 2 := by
  have : Real.sqrt (2 * x) ≤ 0.36 := by
    rw [show (0.36:ℝ) = Real.sqrt (0.36 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem fin_rpow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.rpow x (-(k:ℝ)) = (x ^ k)⁻¹ := by
  show x ^ (-(k:ℝ)) = _
  rw [Real.rpow_neg hx, Real.rpow_natCast]

theorem fin_one_le (μ : ℝ) (h0 : 0 < μ) (h : 1 ≤ μ ^ 2) : 1 ≤ μ := by nlinarith

theorem fin_sq_le (P : ℝ) (h0 : 0 ≤ P) (h : P ^ 2 ≤ 1 / 16) : P ≤ 1 / 4 := by nlinarith

set_option maxHeartbeats 1000000 in
theorem golf_final
    (hT41 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β))
    (hSp : ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (C * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β))
    (hSurj : ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
      (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ),
      0 < p → TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
      TangentSamplingOperatorSurjectiveOnT Omega S)
    (hCert : ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
      (Omega : Finset (Fin n₁ × Fin n₂)),
      SamplingOperatorInjectiveOnT Omega S →
      (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, StrictDualCertificate Omega S Y) →
      IsUniqueMinimizer Omega M)
    (hBer : ∀ {n₁ n₂ : ℕ} (p u : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < p → p ≤ 1 → 0 ≤ u → 0 < frobeniusNormSq X →
      bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|) ≤ 2 * Real.exp (-u))
    (hFix : ∀ (n₁ n₂ m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) (c β : ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 0 < c → 2 < β →
      bernoulliSuccessProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) M ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
      successProb m M ≥
          1 - (2 * c) * Real.rpow (↑(max n₁ n₂)) (-β)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 2 * (n : ℝ) * (r : ℝ) * (Real.log (n : ℝ)) ^ 6 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤ successProb m M := by
  obtain ⟨CT, cT, hCT, hcT, hT⟩ := hT41
  obtain ⟨CS, hCS, hS⟩ := hSp
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 10 * (2 * CT + 96 + 64 * CS ^ 2 + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith [sq_nonneg CS]
  have hA20 : 20 * CT ≤ A := by rw [hA]; linarith [sq_nonneg CS]
  have hA960 : 960 ≤ A := by rw [hA]; linarith [sq_nonneg CS]
  have hA640 : 640 * CS ^ 2 ≤ A := by rw [hA]; linarith [sq_nonneg CS]
  have hA10 : 10 ≤ A := by linarith
  refine ⟨11 * (A + 1) + 22 * (cT + 3) + 100, by linarith, ?_⟩
  intro n r m M S μ hSI hm hC
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = 11 * (A + 1) + 22 * (cT + 3) + 100 := ⟨_, rfl⟩
  rw [← hCd] at hC
  have hC100 : 100 ≤ C := by rw [hCd]; linarith
  have hCA : 11 * (A + 1) ≤ C := by rw [hCd]; linarith
  have hCc : 22 * (cT + 3) ≤ C := by rw [hCd]; linarith
  -- r = 0: every observation set succeeds
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    rw [fin_all_good m M (fin_r0_good S (fun Ω => hCert S Ω)) hm]
    have : (0:ℝ) ≤ 1 / (n:ℝ) ^ 3 := by positivity
    linarith
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    · rw [fin_all_good m M (fun Ω X _ hne => absurd (funext fun i => Fin.elim0 i) hne) hm]
      norm_num
    · have : 0 ≤ successProb m M := by
        unfold successProb; dsimp only
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      norm_num
      exact this
    · exfalso
      have hμ2 : 1 ≤ μ ^ 2 := ctamp_mu_sq S μ hSI.2.2.2 (by norm_num) hrpos
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hrpos
      have hm4' : m ≤ 4 := hm
      have hm4 : (m:ℝ) ≤ 4 := by exact_mod_cast hm4'
      have hl := Real.log_two_gt_d9
      have hl' := hl.le
      have hL6 : (0.11:ℝ) ≤ Real.log 2 ^ 6 := by
        calc (0.11:ℝ) ≤ 0.6931471803 ^ 6 := by norm_num
          _ ≤ Real.log 2 ^ 6 := pow_le_pow_left₀ (by norm_num) hl' 6
      simp only [Nat.cast_ofNat] at hC
      have key : (100:ℝ) * 1 * 2 * 1 * 0.11 ≤ C * μ ^ 2 * 2 * r * Real.log 2 ^ 6 := by
        gcongr
      linarith
  -- main case n ≥ 3, r ≥ 1
  have hn0 : 0 < n := by omega
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0:ℝ) < n := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Real.log (n:ℝ) = L := ⟨_, rfl⟩
  rw [hL] at hC
  have hL1 : 1 ≤ L := by
    rw [← hL]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 ≤ L := by linarith
  have hLn : L ≤ n := by rw [← hL]; have := Real.log_le_sub_one_of_pos hnpos; linarith
  have hμ : 0 < μ := hSI.1
  have hμ2 : 1 ≤ μ ^ 2 := ctamp_mu_sq S μ hSI.2.2.2 hn0 hrpos
  have hμ1 : 1 ≤ μ := fin_one_le μ hμ hμ2
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hrpos
  have hmR : (m:ℝ) ≤ n * n := by exact_mod_cast hm
  have hμr : 1 ≤ μ ^ 2 * r := one_le_mul_of_one_le_of_one_le hμ2 hr1
  have hL26 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL16 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
  have hsmall : C * (μ ^ 2 * r) ≤ n := by
    have h1 : C * μ ^ 2 * n * r * 1 ≤ C * μ ^ 2 * n * r * L ^ 6 :=
      mul_le_mul_of_nonneg_left hL16 (by positivity)
    have h2 : C * (μ ^ 2 * r) * n ≤ n * n := by linarith
    exact le_of_mul_le_mul_right h2 hnpos
  have hCn : C ≤ n := by
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ C) hμr; linarith
  have hμr0 : (0:ℝ) ≤ μ ^ 2 * r := by linarith
  have hμrn : μ ^ 2 * r ≤ n := by
    have := le_mul_of_one_le_left hμr0 (by linarith : (1:ℝ) ≤ C); linarith
  have h2μr : 2 * (μ ^ 2 * r) ≤ n := by
    have := mul_le_mul_of_nonneg_right (by linarith : (2:ℝ) ≤ C) hμr0; linarith
  -- iteration count K
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 3 * Nat.log 2 n + 5 := ⟨_, rfl⟩
  have hKpos : K ≠ 0 := by omega
  have hKL : (K:ℝ) ≤ 11 * L := by
    rw [hK]; push_cast
    have := fin_log2 n hn0; rw [hL] at this; linarith
  have h2K : (4:ℝ) * n ^ 3 ≤ 2 ^ K := by rw [hK]; exact_mod_cast fin_pow n
  -- batch size mq
  obtain ⟨mq, hmqd⟩ : ∃ mq : ℕ, mq = m / K := ⟨_, rfl⟩
  have hmqK : (mq:ℝ) * K ≤ m := by rw [hmqd]; exact_mod_cast Nat.div_mul_le_self m K
  have hmlt : (m:ℝ) < K * (mq + 1) := by
    rw [hmqd]; exact_mod_cast Nat.lt_mul_div_succ m (Nat.pos_of_ne_zero hKpos)
  have hmqn : mq ≤ n * n := by rw [hmqd]; exact (Nat.div_le_self m K).trans hm
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = μ ^ 2 * n * r * L := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by
    rw [hXd]
    have h1 : (1:ℝ) ≤ n * L := one_le_mul_of_one_le_of_one_le (by linarith) hL1
    have := one_le_mul_of_one_le_of_one_le hμr h1
    linarith
  have hX0 : 0 ≤ X := by linarith
  have hAX : A * X < mq := by
    have e1 : (K:ℝ) * (A * X + 1) ≤ 11 * L * ((A + 1) * X) :=
      mul_le_mul hKL (by linarith) (by linarith [mul_nonneg hA0 hX0]) (by linarith)
    have e2 : 11 * L * ((A + 1) * X) = 11 * (A + 1) * (μ ^ 2 * n * r * L ^ 2) := by
      rw [hXd]; ring
    have e3 : 11 * (A + 1) * (μ ^ 2 * n * r * L ^ 2) ≤ C * (μ ^ 2 * n * r * L ^ 6) :=
      mul_le_mul hCA (mul_le_mul_of_nonneg_left hL26 (by positivity)) (by positivity)
        (by linarith)
    have h1 : (K:ℝ) * (A * X + 1) ≤ m := by linarith
    have h2 := lt_of_mul_lt_mul_left (h1.trans_lt hmlt) (Nat.cast_nonneg K)
    linarith
  have hmq0 : (0:ℝ) < mq := by linarith [mul_nonneg hA0 hX0]
  have hmqpos : 0 < mq := by exact_mod_cast hmq0
  have hmq1 : (1:ℝ) ≤ mq := by exact_mod_cast hmqpos
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (mq:ℝ) / ((n:ℝ) * (n:ℝ)) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one (by positivity)]; exact_mod_cast hmqn
  -- rpow conversions
  have hrp10 : Real.rpow (n:ℝ) (-10) = ((n:ℝ) ^ 10)⁻¹ := by
    have := fin_rpow (n:ℝ) hnpos.le 10; simp only [Nat.cast_ofNat] at this; exact this
  have hrp7 : Real.rpow (n:ℝ) (-7) = ((n:ℝ) ^ 7)⁻¹ := by
    have := fin_rpow (n:ℝ) hnpos.le 7; simp only [Nat.cast_ofNat] at this; exact this
  -- tangent sampling concentration (5768a99b)
  have hA0' : A0 S (1 + μ) :=
    ⟨fin_coh S.u μ hμ.le hSI.2.1 hn0 hrpos, fin_coh S.v μ hμ.le hSI.2.2.1 hn0 hrpos⟩
  have hTpre : (mq:ℝ) ≥ CT * (1 + μ) * (↑(max n n)) * (r : ℝ) *
      (10 * Real.log (↑(max n n))) := by
    simp only [max_self]; rw [hL]
    have h1μ : 1 + μ ≤ 2 * μ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hμ1 hμ.le; linarith
    have hb : 0 ≤ (n:ℝ) * r * (10 * L) := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1μ hCT.le) hb
    have h2 : CT * (2 * μ ^ 2) * ((n:ℝ) * r * (10 * L)) = 20 * CT * X := by rw [hXd]; ring
    have h3 : 20 * CT * X ≤ A * X := mul_le_mul_of_nonneg_right hA20 hX0
    linarith
  have hTn := hT CT le_rfl 10 (by norm_num) n n r mq M (1 + μ) μ S hn0 hn0 hrpos hmqn
    (by linarith) hμ1 hA0' hSI.2.2.2 hTpre
  simp only [max_self] at hTn
  rw [← hq, hrp10] at hTn
  have hAa : bernoulliEventProb q (fun t => ¬ TangentSamplingConcentration t S q (1 / 2))
      ≤ cT * ((n:ℝ) ^ 10)⁻¹ := by
    rw [ctamp_compl]; linarith
  -- spectral bound (4905533d)
  have h10nL : 10 * n * L ≤ (mq:ℝ) := by
    have h1 : (10:ℝ) * n * L ≤ 10 * X := by
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hμr) hnpos.le) hL0
      rw [hXd]; linarith
    have h2 : 10 * X ≤ A * X := mul_le_mul_of_nonneg_right hA10 hX0
    linarith
  have hBb : ∀ W : RealMatrix n n, bernoulliEventProb q (fun t =>
      ¬ spectralNorm (centeredSamplingFluctuation t q W)
        ≤ (CS * Real.sqrt (10 * (n:ℝ) * L / q)) * entrySupNorm W) ≤ ((n:ℝ) ^ 10)⁻¹ := by
    intro W
    have hSn := hS 10 (by norm_num) n n mq W hn0 hn0 hmqn
      (by simp only [max_self]; rw [hL]; linarith)
    simp only [max_self] at hSn
    rw [← hq, hL, hrp10] at hSn
    unfold CenteredSamplingSpectralBound at hSn
    rw [ctamp_compl]; linarith
  -- ρ and the Bernstein condition
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = 2 * μ ^ 2 * r / n := ⟨_, rfl⟩
  have hρn : ρ * n = 2 * μ ^ 2 * r := by rw [hρd]; field_simp
  have hρ0 : 0 ≤ ρ := by rw [hρd]; positivity
  have hρ1 : ρ ≤ 1 := by rw [hρd, div_le_one hnpos]; linarith
  have hsr : Real.sqrt r ≤ r := by
    calc Real.sqrt r ≤ Real.sqrt ((r:ℝ) ^ 2) := Real.sqrt_le_sqrt (by
          have := mul_le_mul_of_nonneg_left hr1 (by linarith : (0:ℝ) ≤ r); linarith)
      _ = r := Real.sqrt_sq (by linarith)
  have hρ : (r : ℝ) / n + μ * Real.sqrt r / n ≤ ρ := by
    rw [hρd, show (r : ℝ) / n + μ * Real.sqrt r / n = (r + μ * Real.sqrt r) / n by ring]
    have e1 := mul_le_mul_of_nonneg_left hsr hμ.le
    have e2 := mul_nonneg (mul_nonneg hμ.le (sub_nonneg.2 hμ1)) (by linarith : (0:ℝ) ≤ r)
    have e3 := mul_nonneg (sub_nonneg.2 hμ2) (by linarith : (0:ℝ) ≤ r)
    gcongr
    linarith
  have hk0 : 0 ≤ 2 * ρ + ρ ^ 2 := add_nonneg (by linarith) (sq_nonneg ρ)
  have ex : (2 * ρ + ρ ^ 2) / q * (10 * L) = (2 * ρ + ρ ^ 2) * (n * n) * (10 * L) / mq := by
    rw [hq]; field_simp
  have hbound : 16 * ((2 * ρ + ρ ^ 2) * (n * n) * (10 * L)) ≤ mq := by
    have h3 : 2 * ρ + ρ ^ 2 ≤ 3 * ρ := by
      have := mul_le_mul_of_nonneg_left hρ1 hρ0; linarith
    calc 16 * ((2 * ρ + ρ ^ 2) * (n * n) * (10 * L))
        ≤ 16 * ((3 * ρ) * (n * n) * (10 * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h3 (by positivity)) (by linarith)) (by norm_num)
      _ = 960 * X := by rw [hXd]; linear_combination (480 * (n:ℝ) * L) * hρn
      _ ≤ A * X := mul_le_mul_of_nonneg_right hA960 hX0
      _ ≤ mq := hAX.le
  have hx16 : (2 * ρ + ρ ^ 2) / q * (10 * L) ≤ 1 / 16 := by
    rw [ex, div_le_iff₀ hmq0]; linarith
  have hx0 : 0 ≤ (2 * ρ + ρ ^ 2) / q * (10 * L) :=
    mul_nonneg (div_nonneg hk0 hq0.le) (by linarith)
  have hcond : Real.sqrt (2 * ((2 * ρ + ρ ^ 2) / q) * (10 * L))
      + (2 / 3) * ((2 * ρ + ρ ^ 2) / q) * (10 * L) ≤ 1 / 2 := by
    have := fin_cond _ hx0 hx16
    simpa only [mul_assoc] using this
  -- the numeric condition hnum
  have hlam : 0 ≤ CS * Real.sqrt (10 * (n:ℝ) * L / q) := mul_nonneg hCS.le (Real.sqrt_nonneg _)
  have hsI : entrySupNorm (signMatrix S) ≤ μ * Real.sqrt ((r:ℝ) / ((n:ℝ) * n)) :=
    fin_entry_le _ _ hn0 hn0 hSI.2.2.2
  have hP0 : 0 ≤ 2 * (CS * Real.sqrt (10 * (n:ℝ) * L / q)) * (μ * Real.sqrt ((r:ℝ) / ((n:ℝ) * n))) :=
    mul_nonneg (mul_nonneg (by norm_num) hlam) (mul_nonneg hμ.le (Real.sqrt_nonneg _))
  have hP2 : (2 * (CS * Real.sqrt (10 * (n:ℝ) * L / q)) * (μ * Real.sqrt ((r:ℝ) / ((n:ℝ) * n)))) ^ 2
      = 40 * CS ^ 2 * X / mq := by
    have g1 : 0 ≤ 10 * (n:ℝ) * L / q := div_nonneg (by positivity) hq0.le
    have g2 : 0 ≤ (r:ℝ) / ((n:ℝ) * n) := by positivity
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt g1, Real.sq_sqrt g2, hq, hXd]
    field_simp
    ring
  have hP : 2 * (CS * Real.sqrt (10 * (n:ℝ) * L / q)) * (μ * Real.sqrt ((r:ℝ) / ((n:ℝ) * n)))
      ≤ 1 / 4 := by
    have h1 : 40 * CS ^ 2 * X / mq ≤ 1 / 16 := by
      rw [div_le_iff₀ hmq0]
      have := mul_le_mul_of_nonneg_right hA640 hX0
      linarith
    exact fin_sq_le _ hP0 (by rw [hP2]; exact h1)
  have hF : frobeniusNorm (signMatrix S) ≤ n := by
    unfold frobeniusNorm
    have h1 := fin_frobSq_le (signMatrix S) _ hSI.2.2.2
    have h2 : (n:ℝ) * n * (μ * Real.sqrt ((r:ℝ) / ((n:ℝ) * n))) ^ 2 = μ ^ 2 * r := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp
    calc Real.sqrt (frobeniusNormSq (signMatrix S)) ≤ Real.sqrt ((n:ℝ) * n) :=
          Real.sqrt_le_sqrt (by
            have := le_mul_of_one_le_left hnpos.le (by linarith : (1:ℝ) ≤ n); linarith)
      _ = n := Real.sqrt_mul_self hnpos.le
  have hF0 : 0 ≤ frobeniusNorm (signMatrix S) := Real.sqrt_nonneg _
  have hpart2 : 2 * ((1 / 2) ^ K * frobeniusNorm (signMatrix S)) / q ≤ 1 / 2 := by
    have hhalf : ((1:ℝ) / 2) ^ K = 1 / 2 ^ K := by rw [div_pow, one_pow]
    have h2K' : (0:ℝ) < 2 ^ K := by positivity
    have key : 2 * (1 / 2 ^ K * frobeniusNorm (signMatrix S)) * ((n:ℝ) * n) ≤ 1 / 2 * mq := by
      rw [show 2 * (1 / 2 ^ K * frobeniusNorm (signMatrix S)) * ((n:ℝ) * n)
          = 2 * frobeniusNorm (signMatrix S) * ((n:ℝ) * n) / 2 ^ K by ring, div_le_iff₀ h2K']
      calc 2 * frobeniusNorm (signMatrix S) * ((n:ℝ) * n) ≤ 2 * n * ((n:ℝ) * n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (by norm_num))
              (by positivity)
        _ = 1 / 2 * (4 * n ^ 3) := by ring
        _ ≤ 1 / 2 * 2 ^ K := by linarith
        _ ≤ 1 / 2 * mq * 2 ^ K := by
            have := mul_le_mul_of_nonneg_right hmq1 h2K'.le; linarith
    rw [hhalf, hq, div_div_eq_mul_div, div_le_iff₀ hmq0]
    exact key
  have hE := mul_le_mul_of_nonneg_left hsI (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlam)
  have hnum : 2 * (CS * Real.sqrt (10 * (n:ℝ) * L / q)) * entrySupNorm (signMatrix S)
      + 2 * ((1 / 2) ^ K * frobeniusNorm (signMatrix S)) / q < 1 := by
    linarith
  -- golfing
  have hG := golf_square S μ hSI q (CS * Real.sqrt (10 * (n:ℝ) * L / q)) (cT * ((n:ℝ) ^ 10)⁻¹)
    (((n:ℝ) ^ 10)⁻¹) (10 * L) ρ hq0 hq1 hlam K hKpos (by linarith) hρ0 hρ
    (fun Ω h => hSurj Ω S q hq0 h) (fun Ω h1 h2 => hCert S Ω h1 h2)
    (fun p u X h1 h2 h3 h4 => hBer p u X h1 h2 h3 h4) hcond hAa hBb hnum
  have hexp : Real.exp (-(10 * L)) = ((n:ℝ) ^ 10)⁻¹ := by
    rw [Real.exp_neg, ← hL, show (10:ℝ) * Real.log n = Real.log ((n:ℝ) ^ 10) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  rw [hexp] at hG
  have hN0 : (0:ℝ) < ((n:ℝ) ^ 10)⁻¹ := by positivity
  have hnn : (1:ℝ) ≤ n * n := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hfail : (K:ℝ) * (cT * ((n:ℝ) ^ 10)⁻¹ + (n:ℝ) * n * (2 * ((n:ℝ) ^ 10)⁻¹) + ((n:ℝ) ^ 10)⁻¹)
      ≤ 11 * (cT + 3) * ((n:ℝ) ^ 7)⁻¹ := by
    have h1 : cT * ((n:ℝ) ^ 10)⁻¹ + (n:ℝ) * n * (2 * ((n:ℝ) ^ 10)⁻¹) + ((n:ℝ) ^ 10)⁻¹
        ≤ (cT + 3) * ((n:ℝ) * n) * ((n:ℝ) ^ 10)⁻¹ := by
      linarith [mul_nonneg (mul_nonneg hcT.le hN0.le) (sub_nonneg.2 hnn),
        mul_nonneg hN0.le (sub_nonneg.2 hnn)]
    have h2 : (K:ℝ) ≤ 11 * n := by linarith
    have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    have h4 : (K:ℝ) * ((cT + 3) * ((n:ℝ) * n) * ((n:ℝ) ^ 10)⁻¹)
        ≤ 11 * n * ((cT + 3) * ((n:ℝ) * n) * ((n:ℝ) ^ 10)⁻¹) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hN0.le)
    have h5 : 11 * (n:ℝ) * ((cT + 3) * ((n:ℝ) * n) * ((n:ℝ) ^ 10)⁻¹)
        = 11 * (cT + 3) * ((n:ℝ) ^ 7)⁻¹ := by
      field_simp
    linarith
  -- monotone transfer to p = m / n²
  have hq'0 : 0 ≤ 1 - (1 - q) ^ K := by
    have := pow_le_one₀ (n := K) (by linarith : (0:ℝ) ≤ 1 - q) (by linarith : 1 - q ≤ 1)
    linarith
  have hq'p : 1 - (1 - q) ^ K ≤ (m:ℝ) / ((n:ℝ) * (n:ℝ)) := by
    have hb := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ -q) K
    rw [← sub_eq_add_neg] at hb
    have hKq : (K:ℝ) * q ≤ (m:ℝ) / ((n:ℝ) * (n:ℝ)) := by
      rw [hq, ← mul_div_assoc]
      gcongr
      linarith
    linarith
  have hp1 : (m:ℝ) / ((n:ℝ) * (n:ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; exact hmR
  have hmono : ∀ Ω Ω' : Finset (Fin n × Fin n), Ω ⊆ Ω' →
      IsUniqueMinimizer Ω M → IsUniqueMinimizer Ω' M :=
    fun Ω Ω' hs h X hX hne => h X (fun p hp => hX p (hs hp)) hne
  have hanti : bernoulliEventProb ((m:ℝ) / ((n:ℝ) * (n:ℝ))) (fun Ω => ¬ IsUniqueMinimizer Ω M)
      ≤ bernoulliEventProb (1 - (1 - q) ^ K) (fun Ω => ¬ IsUniqueMinimizer Ω M) :=
    ctamp_fail_antitone _ _ hq'0 hq'p hp1 (fun Ω => IsUniqueMinimizer Ω M) hmono
  have hcomp : bernoulliEventProb ((m:ℝ) / ((n:ℝ) * (n:ℝ))) (fun Ω => ¬ IsUniqueMinimizer Ω M)
      = 1 - bernoulliSuccessProb ((m:ℝ) / ((n:ℝ) * (n:ℝ))) M :=
    ctamp_compl _ (fun Ω => IsUniqueMinimizer Ω M)
  have hbs : bernoulliSuccessProb ((m:ℝ) / ((n:ℝ) * (n:ℝ))) M ≥
      1 - (11 * (cT + 3)) * Real.rpow (↑(max n n)) (-7) := by
    rw [max_self, hrp7]; linarith
  have hres := hFix n n m M (11 * (cT + 3)) 7 hn0 hn0 hm (by linarith) (by norm_num) hbs
  rw [max_self, hrp7] at hres
  have hfin : 2 * (11 * (cT + 3)) * ((n:ℝ) ^ 7)⁻¹ ≤ 1 / (n:ℝ) ^ 3 := by
    have hk : 2 * (11 * (cT + 3)) ≤ (n:ℝ) := by linarith
    calc 2 * (11 * (cT + 3)) * ((n:ℝ) ^ 7)⁻¹ ≤ n * ((n:ℝ) ^ 7)⁻¹ :=
          mul_le_mul_of_nonneg_right hk (by positivity)
      _ = 1 / (n:ℝ) ^ 6 := by field_simp
      _ ≤ 1 / (n:ℝ) ^ 3 :=
          one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ n) (by norm_num))
  linarith

open MatrixCompletion in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 2 * (n : ℝ) * (r : ℝ) * (Real.log (n : ℝ)) ^ 6 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤ successProb m M := by
  exact golf_final candes_recht_theorem41_bernoulli_tangent_sampling_concentration
    fixed_matrix_centered_sampling_spectral_bound
    tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
    dual_certificate_with_restricted_sampling_implies_unique_completion
    bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
    fixed_cardinality_completion_probability_from_bernoulli_model
