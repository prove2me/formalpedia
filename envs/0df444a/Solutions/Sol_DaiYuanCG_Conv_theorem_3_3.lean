-- Prove2me | solution 1 for DaiYuanCG.Conv.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:03:12.947524+00:00
-- url     : https://prove2.me/submissions/39c10b81-3ec2-47c5-abdc-6022f3e94097

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

set_option autoImplicit false

namespace DYProof
open DaiYuanCG.Conv

variable {n : ℕ}

/-- `‖d_k‖² / (g_kᵀ d_k)²`. -/
noncomputable def U (f : E n → ℝ) (x d : ℕ → E n) (k : ℕ) : ℝ :=
  ‖d k‖ ^ 2 / (inner ℝ (gradient f (x k)) (d k)) ^ 2

theorem alg1 (G A B : ℝ) (h : B - A ≠ 0) : -G + G / (B - A) * B = G / (B - A) * A := by
  field_simp
  ring

theorem alg2 (β a D G : ℝ) (hβ : 0 < β) (ha : a < 0) (hG : 0 < G) :
    (β ^ 2 * D - 2 * (β * a) - G) / (β * a) ^ 2 ≤ D / a ^ 2 + 1 / G := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have ha0 : a ≠ 0 := ha.ne
  have hG0 : G ≠ 0 := hG.ne'
  have h : D / a ^ 2 + 1 / G - (β ^ 2 * D - 2 * (β * a) - G) / (β * a) ^ 2 =
      (β * a + G) ^ 2 / (G * (β * a) ^ 2) := by
    field_simp
    ring
  have h2 : 0 ≤ (β * a + G) ^ 2 / (G * (β * a) ^ 2) := by positivity
  linarith

theorem dy_eq (f : E n → ℝ) (x d : ℕ → E n) (k : ℕ) :
    inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) =
      inner ℝ (gradient f (x (k + 1))) (d k) - inner ℝ (gradient f (x k)) (d k) := by
  rw [inner_sub_right, real_inner_comm (gradient f (x (k + 1))) (d k),
    real_inner_comm (gradient f (x k)) (d k)]

theorem step_facts (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hrun : IsDYRun f δ σ x d α) (k : ℕ) (hk : 1 ≤ k)
    (hneg : inner ℝ (gradient f (x k)) (d k) < 0)
    (hg : gradient f (x (k + 1)) ≠ 0) :
    0 < inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ∧
    0 < betaDY f x d k ∧
    inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
      betaDY f x d k * inner ℝ (gradient f (x k)) (d k) := by
  obtain ⟨⟨-, hit⟩, hw⟩ := hrun
  obtain ⟨-, hx, hd⟩ := hit k hk
  obtain ⟨-, hcurv⟩ := hw k hk
  rw [← hx] at hcurv
  have hdy := dy_eq f x d k
  have hpos : 0 < inner ℝ (gradient f (x (k + 1))) (d k) - inner ℝ (gradient f (x k)) (d k) := by
    nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hσ1) hneg]
  have hG : 0 < ‖gradient f (x (k + 1))‖ ^ 2 := by
    have := norm_pos_iff.mpr hg
    positivity
  have hβ : betaDY f x d k = ‖gradient f (x (k + 1))‖ ^ 2 /
      (inner ℝ (gradient f (x (k + 1))) (d k) - inner ℝ (gradient f (x k)) (d k)) := by
    unfold betaDY
    rw [hdy]
  refine ⟨by rw [hdy]; exact hpos, ?_, ?_⟩
  · rw [hβ]
    exact div_pos hG hpos
  · rw [hd, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq, inner_smul_right, hβ]
    exact alg1 _ _ _ hpos.ne'

theorem descent (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hrun : IsDYRun f δ σ x d α) (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [hrun.1.1, inner_neg_right, real_inner_self_eq_norm_sq]
    have := norm_pos_iff.mpr (hnt 1 le_rfl)
    exact neg_neg_of_pos (pow_pos this 2)
  | succ k hk ih =>
    obtain ⟨-, hβ, heq⟩ := step_facts f δ σ hσ1 x d α hrun k hk ih (hnt (k + 1) (by omega))
    rw [heq]
    exact mul_neg_of_pos_of_neg hβ ih

theorem decrease (f : E n → ℝ) (δ σ : ℝ) (hδ : 0 < δ) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hrun : IsDYRun f δ σ x d α)
    (hdesc : ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0) :
    ∀ k, 1 ≤ k → f (x (k + 1)) < f (x k) := by
  intro k hk
  obtain ⟨hα, hx, -⟩ := hrun.1.2 k hk
  obtain ⟨hw1, -⟩ := hrun.2 k hk
  rw [← hx] at hw1
  have h1 := hdesc k hk
  have h2 : 0 < δ * α k := mul_pos hδ hα
  nlinarith [mul_neg_of_pos_of_neg h2 h1]

theorem level (f : E n → ℝ) (x : ℕ → E n)
    (hdec : ∀ k, 1 ≤ k → f (x (k + 1)) < f (x k)) :
    ∀ k, 1 ≤ k → f (x k) ≤ f (x 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (hdec k hk).le.trans ih

theorem zout_step (f : E n → ℝ) (N : Set (E n)) (L : ℝ) (δ σ : ℝ) (hδ : 0 < δ)
    (hσ1 : σ < 1) (x d : ℕ → E n) (α : ℕ → ℝ) (hA : Assumption31 f (x 1) N L)
    (hrun : IsDYRun f δ σ x d α)
    (hdesc : ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0)
    (hlev : ∀ k, 1 ≤ k → f (x k) ≤ f (x 1)) (k : ℕ) (hk : 1 ≤ k) :
    δ * (1 - σ) / L / U f x d k ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨-, -, hLN, -, -, hL, hlip⟩ := hA
  obtain ⟨hαpos, hx, -⟩ := hrun.1.2 k hk
  obtain ⟨hw1, hcurv⟩ := hrun.2 k hk
  rw [← hx] at hw1 hcurv
  have ha := hdesc k hk
  have hxk : x k ∈ N := hLN (hlev k hk)
  have hxk1 : x (k + 1) ∈ N := hLN (hlev (k + 1) (by omega))
  have hlipk := hlip _ hxk1 _ hxk
  have hdiff : x (k + 1) - x k = α k • d k := by rw [hx]; simp
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hαpos] at hlipk
  have hcs := real_inner_le_norm (d k) (gradient f (x (k + 1)) - gradient f (x k))
  have hdy := dy_eq f x d k
  have hdne : d k ≠ 0 := by
    rintro h
    rw [h, inner_zero_right] at ha
    exact lt_irrefl _ ha
  have hD : 0 < ‖d k‖ := norm_pos_iff.mpr hdne
  have hmul := mul_le_mul_of_nonneg_left hlipk hD.le
  have key : (1 - σ) * (-(inner ℝ (gradient f (x k)) (d k))) ≤ L * α k * ‖d k‖ ^ 2 := by
    nlinarith
  set a := inner ℝ (gradient f (x k)) (d k) with ha_def
  set D := ‖d k‖ with hD_def
  have hU : U f x d k = D ^ 2 / a ^ 2 := rfl
  rw [hU]
  have hD2 : 0 < D ^ 2 := by positivity
  have ha0 : a ≠ 0 := ha.ne
  have hcoef : 0 ≤ δ * (-a) / (L * D ^ 2) := by
    apply div_nonneg
    · nlinarith
    · positivity
  have e1 : δ * (1 - σ) / L / (D ^ 2 / a ^ 2) = δ * (-a) / (L * D ^ 2) * ((1 - σ) * (-a)) := by
    field_simp
  have e2 : δ * (-a) / (L * D ^ 2) * (L * α k * D ^ 2) = δ * α k * (-a) := by
    field_simp
  rw [e1]
  calc δ * (-a) / (L * D ^ 2) * ((1 - σ) * (-a))
      ≤ δ * (-a) / (L * D ^ 2) * (L * α k * D ^ 2) := mul_le_mul_of_nonneg_left key hcoef
    _ = δ * α k * (-a) := e2
    _ ≤ f (x k) - f (x (k + 1)) := by linarith

theorem u_step (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hrun : IsDYRun f δ σ x d α) (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0)
    (hdesc : ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0) (k : ℕ) (hk : 1 ≤ k) :
    U f x d (k + 1) ≤ U f x d k + 1 / ‖gradient f (x (k + 1))‖ ^ 2 := by
  have ha := hdesc k hk
  have hg := hnt (k + 1) (by omega)
  obtain ⟨-, hβpos, ht⟩ := step_facts f δ σ hσ1 x d α hrun k hk ha hg
  obtain ⟨-, -, hd⟩ := hrun.1.2 k hk
  have hnorm : ‖d (k + 1)‖ ^ 2 = (betaDY f x d k) ^ 2 * ‖d k‖ ^ 2
      - 2 * inner ℝ (gradient f (x (k + 1))) (d (k + 1)) - ‖gradient f (x (k + 1))‖ ^ 2 := by
    rw [hd, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq, inner_smul_right,
      norm_add_sq_real, inner_neg_left, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hG : 0 < ‖gradient f (x (k + 1))‖ ^ 2 := by
    have := norm_pos_iff.mpr hg
    positivity
  unfold U
  rw [hnorm, ht]
  exact alg2 _ _ _ _ hβpos ha hG

end DYProof

open DaiYuanCG.Conv in
theorem solution {n : ℕ} (f : E n → ℝ) (N : Set (E n)) (L : ℝ)
    (δ σ : ℝ) (hδ : 0 < δ) (hδσ : δ < σ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hA : Assumption31 f (x 1) N L)
    (hrun : IsDYRun f δ σ x d α) (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    LiminfGradZero f x := by
  have hdesc := DYProof.descent f δ σ hσ1 x d α hrun hnt
  have hdec := DYProof.decrease f δ σ hδ x d α hrun hdesc
  have hlev := DYProof.level f x hdec
  have hL : 0 < L := hA.2.2.2.2.2.1
  obtain ⟨b0, hb0⟩ := hA.1
  have hb : ∀ y, b0 ≤ f y := fun y => hb0 ⟨y, rfl⟩
  intro ε hε K
  by_contra hcon
  push_neg at hcon
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  have hupos : ∀ k, 1 ≤ k → 0 < DYProof.U f x d k := by
    intro k hk
    have ha := hdesc k hk
    have hdne : d k ≠ 0 := by
      rintro h
      rw [h, inner_zero_right] at ha
      exact lt_irrefl _ ha
    have hD : 0 < ‖d k‖ := norm_pos_iff.mpr hdne
    have ha0 : inner ℝ (gradient f (x k)) (d k) ≠ 0 := ha.ne
    unfold DYProof.U
    positivity
  set B : ℝ := 1 / ε ^ 2 with hB
  have hB0 : 0 < B := by positivity
  have hubound : ∀ k, K' ≤ k → DYProof.U f x d k ≤ DYProof.U f x d K' + ((k : ℝ) - K') * B := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h1 : 1 ≤ k := le_trans hK'1 hk
      have hs := DYProof.u_step f δ σ hσ1 x d α hrun hnt hdesc k h1
      have hg : ε ≤ ‖gradient f (x (k + 1))‖ := hcon (k + 1) (by omega)
      have hgg : 1 / ‖gradient f (x (k + 1))‖ ^ 2 ≤ B :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε.le hg 2)
      push_cast
      linarith
  set M : ℝ := DYProof.U f x d K' + B with hM
  have hM0 : 0 < M := by have := hupos K' hK'1; positivity
  have hUM : ∀ j : ℕ, DYProof.U f x d (j + K') ≤ M * ((j + K' : ℕ) : ℝ) := by
    intro j
    have h := hubound (j + K') (by omega)
    have hu0 := (hupos K' hK'1).le
    have hk1 : (1 : ℝ) ≤ ((j + K' : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + K')
    have hK0 : (0 : ℝ) ≤ (K' : ℝ) := by positivity
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hk1), mul_nonneg hK0 hB0.le]
  set c : ℝ := δ * (1 - σ) / L with hc
  have hc0 : 0 < c := by
    apply div_pos _ hL
    exact mul_pos hδ (by linarith)
  have hsum : ∀ m : ℕ, ∑ j ∈ Finset.range m, c / DYProof.U f x d (j + K') ≤
      f (x K') - f (x (m + K')) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hz := DYProof.zout_step f N L δ σ hδ hσ1 x d α hA hrun hdesc hlev (m + K')
        (by omega)
      have e : m + 1 + K' = m + K' + 1 := by omega
      rw [e]
      linarith
  let t : ℕ → ℝ := fun j => c / (M * ((j + K' : ℕ) : ℝ))
  have hpos' : ∀ j : ℕ, (0 : ℝ) < ((j + K' : ℕ) : ℝ) := fun j => Nat.cast_pos.mpr (by omega)
  have ht0 : ∀ j, 0 ≤ t j := fun j => by
    have := hpos' j
    positivity
  have htle : ∀ j, t j ≤ c / DYProof.U f x d (j + K') := fun j =>
    div_le_div_of_nonneg_left hc0.le (hupos (j + K') (by omega)) (hUM j)
  have hts : Summable t := by
    refine summable_of_sum_range_le ht0 (c := f (x 1) - b0) (fun m => ?_)
    calc ∑ j ∈ Finset.range m, t j ≤ ∑ j ∈ Finset.range m, c / DYProof.U f x d (j + K') :=
          Finset.sum_le_sum (fun j _ => htle j)
      _ ≤ f (x K') - f (x (m + K')) := hsum m
      _ ≤ f (x 1) - b0 := by linarith [hlev K' hK'1, hb (x (m + K'))]
  have hs2 : Summable (fun j : ℕ => 1 / (((j + K' : ℕ) : ℝ))) := by
    refine (hts.mul_left (M / c)).congr (fun j => ?_)
    have := hpos' j
    simp only [t]
    field_simp
  have hs3 := (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) K').mp hs2
  exact Real.not_summable_one_div_natCast hs3
