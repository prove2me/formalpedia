-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_radial_transversality
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T21:26:50.023493+00:00
-- url     : https://prove2.me/submissions/88b3fe0f-04c0-4107-abc6-00d27697fbc7

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_ball_radial_force_negative
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_ball_radial_convexity
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_effective_potential_bound
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_avoids_second_collision
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open BirkhoffGlobalSection

lemma om_hasDerivAt (μ κ ρ : ℝ) (hρ : 0 < ρ) (hQ : 0 < ρ ^ 2 - 2 * ρ * κ + 1) :
    HasDerivAt (fun r : ℝ => (r ^ 2 - 2 * μ * r * κ + μ ^ 2) / 2 + (1 - μ) / r +
        μ / Real.sqrt (r ^ 2 - 2 * r * κ + 1))
      (ρ - μ * κ - (1 - μ) / ρ ^ 2 -
        μ * (ρ - κ) / Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 3) ρ := by
  have hx := hasDerivAt_id' ρ
  have hQd : HasDerivAt (fun r : ℝ => r ^ 2 - 2 * r * κ + 1) (2 * ρ - 2 * κ) ρ := by
    have := ((hx.fun_pow 2).fun_sub ((hx.const_mul 2).mul_const κ)).add_const 1
    exact this.congr_deriv (by ring)
  have hS := hQd.sqrt hQ.ne'
  set S := Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) with hSdef
  have hSpos : 0 < S := Real.sqrt_pos.2 hQ
  have hsq : S ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1 := Real.sq_sqrt hQ.le
  have h1 := ((((hx.fun_pow 2).fun_sub ((hx.const_mul (2 * μ)).mul_const κ)).add_const (μ ^ 2)).div_const 2)
  have h2 := (hasDerivAt_const ρ (1 - μ)).fun_div hx hρ.ne'
  have h3 := (hasDerivAt_const ρ μ).fun_div hS hSpos.ne'
  refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
  rw [← hSdef]
  field_simp
  linear_combination (0:ℝ) * hsq

lemma dom_hasDerivAt (μ κ ρ : ℝ) (hρ : 0 < ρ) (hQ : 0 < ρ ^ 2 - 2 * ρ * κ + 1) :
    HasDerivAt (fun r : ℝ => r - μ * κ - (1 - μ) / r ^ 2 -
        μ * (r - κ) / Real.sqrt (r ^ 2 - 2 * r * κ + 1) ^ 3)
      (1 + 2 * (1 - μ) / ρ ^ 3 + μ * (3 * (ρ - κ) ^ 2 - (ρ ^ 2 - 2 * ρ * κ + 1)) /
        Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 5) ρ := by
  have hx := hasDerivAt_id' ρ
  have hQd : HasDerivAt (fun r : ℝ => r ^ 2 - 2 * r * κ + 1) (2 * ρ - 2 * κ) ρ := by
    have := ((hx.fun_pow 2).fun_sub ((hx.const_mul 2).mul_const κ)).add_const 1
    exact this.congr_deriv (by ring)
  have hS := (hQd.sqrt hQ.ne').fun_pow 3
  set S := Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) with hSdef
  have hSpos : 0 < S := Real.sqrt_pos.2 hQ
  have hsq : S ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1 := Real.sq_sqrt hQ.le
  have h1 := (hx.sub_const (μ * κ))
  have h2 := (hasDerivAt_const ρ (1 - μ)).fun_div (hx.fun_pow 2) (by positivity)
  have h3 := ((hx.sub_const κ).const_mul μ).fun_div hS (by positivity)
  refine ((h1.fun_sub h2).fun_sub h3).congr_deriv ?_
  rw [← hSdef]
  field_simp
  linear_combination (-(ρ ^ 4 * μ * S ^ 2)) * hsq

lemma key_radial_ineq (μ κ ρ d c : ℝ) (hρ : 0 < ρ) (hρd : ρ < d) (hd1 : d < 1)
    (hκ1 : κ ≤ 1)
    (hF : ∀ r : ℝ, 0 < r → r < d →
      r - μ * κ - (1 - μ) / r ^ 2 - μ * (r - κ) / Real.sqrt (r ^ 2 - 2 * r * κ + 1) ^ 3 < 0)
    (hFF : ∀ r : ℝ, 0 < r → r < d →
      1 ≤ 1 + 2 * (1 - μ) / r ^ 3 + μ * (3 * (r - κ) ^ 2 - (r ^ 2 - 2 * r * κ + 1)) /
        Real.sqrt (r ^ 2 - 2 * r * κ + 1) ^ 5)
    (hcirc : (d ^ 2 - 2 * μ * d * κ + μ ^ 2) / 2 + (1 - μ) / d +
        μ / Real.sqrt (d ^ 2 - 2 * d * κ + 1) < c) :
    2 * ((ρ ^ 2 - 2 * μ * ρ * κ + μ ^ 2) / 2 + (1 - μ) / ρ +
        μ / Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) - c) <
      (ρ - μ * κ - (1 - μ) / ρ ^ 2 -
        μ * (ρ - κ) / Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 3) ^ 2 := by
  set Om : ℝ → ℝ := fun r => (r ^ 2 - 2 * μ * r * κ + μ ^ 2) / 2 + (1 - μ) / r +
        μ / Real.sqrt (r ^ 2 - 2 * r * κ + 1) with hOm
  set F : ℝ → ℝ := fun r => r - μ * κ - (1 - μ) / r ^ 2 -
        μ * (r - κ) / Real.sqrt (r ^ 2 - 2 * r * κ + 1) ^ 3 with hFdef
  set FF : ℝ → ℝ := fun r => 1 + 2 * (1 - μ) / r ^ 3 +
        μ * (3 * (r - κ) ^ 2 - (r ^ 2 - 2 * r * κ + 1)) /
        Real.sqrt (r ^ 2 - 2 * r * κ + 1) ^ 5 with hFFdef
  have hQ : ∀ r : ℝ, 0 < r → r < 1 → 0 < r ^ 2 - 2 * r * κ + 1 := by
    intro r hr0 hr1; nlinarith
  have hdOm : ∀ r : ℝ, 0 < r → r < 1 → HasDerivAt Om (F r) r := fun r hr0 hr1 =>
    om_hasDerivAt μ κ r hr0 (hQ r hr0 hr1)
  have hdF : ∀ r : ℝ, 0 < r → r < 1 → HasDerivAt F (FF r) r := fun r hr0 hr1 =>
    dom_hasDerivAt μ κ r hr0 (hQ r hr0 hr1)
  set φ : ℝ → ℝ := fun r => F r ^ 2 - 2 * Om r with hφ
  have hdφ : ∀ r : ℝ, 0 < r → r < 1 →
      HasDerivAt φ (2 * F r * FF r - 2 * F r) r := by
    intro r hr0 hr1
    have := ((hdF r hr0 hr1).fun_pow 2).fun_sub ((hdOm r hr0 hr1).const_mul 2)
    exact this.congr_deriv (by simp)
  have hanti : AntitoneOn φ (Set.Icc ρ d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ρ d)
    · intro r hr
      exact (hdφ r (by linarith [hr.1]) (by linarith [hr.2])).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hdφ r (by linarith [hr.1]) (by linarith [hr.2])).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := by linarith [hr.1]
      rw [(hdφ r hr0 (by linarith [hr.2])).deriv]
      have h1 := hF r hr0 hr.2
      have h2 := hFF r hr0 hr.2
      have : F r * (FF r - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1.le (by simp only [FF]; linarith)
      nlinarith
  have hle := hanti ⟨le_rfl, hρd.le⟩ ⟨hρd.le, le_rfl⟩ hρd.le
  simp only [φ] at hle
  have hcirc' : Om d < c := hcirc
  show 2 * (Om ρ - c) < F ρ ^ 2
  nlinarith [sq_nonneg (F d)]

lemma lc_radial_hasDerivAt (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i))
      ((s 2 ^ 2 + s 3 ^ 2) + 2 * c * (s 0 ^ 2 + s 1 ^ 2)
        + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2)
        - 2 * μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s)
        + μ * (s 0 ^ 2 + s 1 ^ 2) * (8 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 - s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3) 1 := by
  have hx := hasDerivAt_id' (1 : ℝ)
  have e : ∀ i : Fin 4, HasDerivAt (fun a : ℝ => a * s i) (1 * s i) 1 := fun i => hx.mul_const (s i)
  have hin : HasDerivAt (fun a : ℝ => (2 * ((a * s 0) ^ 2 - (a * s 1) ^ 2) - 1) ^ 2 +
      (4 * (a * s 0) * (a * s 1)) ^ 2)
      (8 * (s 0 ^ 2 - s 1 ^ 2) * (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) + 64 * (s 0 * s 1) ^ 2) 1 := by
    have := ((((((e 0).fun_pow 2).fun_sub ((e 1).fun_pow 2)).const_mul 2).sub_const 1).fun_pow 2).fun_add
      ((((e 0).const_mul 4).fun_mul (e 1)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * ((1 * s 0) ^ 2 - (1 * s 1) ^ 2) - 1) ^ 2 + (4 * (1 * s 0) * (1 * s 1)) ^ 2 ≠ 0 := by
    simp only [one_mul]; exact hD.ne'
  have hS := hin.sqrt hD'
  simp only [one_mul] at hS
  unfold secondCollisionDistanceSq at hD ⊢
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 2 =
      (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 :=
    Real.sq_sqrt hD.le
  have hW := ((((e 2).fun_pow 2).fun_add ((e 3).fun_pow 2)).div_const 2)
  have hP := (((e 0).fun_pow 2).fun_add ((e 1).fun_pow 2))
  have hL := (((e 0).fun_mul (e 3)).fun_sub ((e 1).fun_mul (e 2)))
  have hM := (((e 0).fun_mul (e 3)).fun_add ((e 1).fun_mul (e 2)))
  have htot := ((((hW.fun_add (hP.const_mul c)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul hL)).fun_sub (hM.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS (by simpa using hNpos.ne'))
  refine htot.congr_deriv ?_
  simp only [one_mul]
  generalize hNdef : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  linear_combination (0:ℝ) * hsq

set_option maxHeartbeats 1000000 in
lemma lc_R_pos (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s)
    (hH : leviCivitaHamiltonian μ c s = 0) (hP : 0 < s 0 ^ 2 + s 1 ^ 2)
    (hF : 2 * (s 0 ^ 2 + s 1 ^ 2) - μ * ((s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2))
        - (1 - μ) / (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2
        - μ * (2 * (s 0 ^ 2 + s 1 ^ 2) - (s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3 < 0)
    (hkey : 2 * (((2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2
          - 2 * μ * (2 * (s 0 ^ 2 + s 1 ^ 2)) * ((s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2))
          + μ ^ 2) / 2 + (1 - μ) / (2 * (s 0 ^ 2 + s 1 ^ 2))
          + μ / Real.sqrt (secondCollisionDistanceSq s) - c) <
      (2 * (s 0 ^ 2 + s 1 ^ 2) - μ * ((s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2))
        - (1 - μ) / (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2
        - μ * (2 * (s 0 ^ 2 + s 1 ^ 2) - (s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3) ^ 2) :
    0 < (s 2 ^ 2 + s 3 ^ 2) + 2 * c * (s 0 ^ 2 + s 1 ^ 2)
        + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2)
        - 2 * μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s)
        + μ * (s 0 ^ 2 + s 1 ^ 2) * (8 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 - s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3 := by
  unfold leviCivitaHamiltonian zNormSq wNormSq at hH
  have hNpos : 0 < Real.sqrt (secondCollisionDistanceSq s) := Real.sqrt_pos.2 hD
  generalize Real.sqrt (secondCollisionDistanceSq s) = N at *
  have hP0 : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := hP.ne'
  have e2 : (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 * (2 * (((2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 - 2 * μ * (2 * (s 0 ^ 2 + s 1 ^ 2)) * ((s 0 ^ 2 - s 1 ^ 2) / (s 0 ^ 2 + s 1 ^ 2)) + μ ^ 2) / 2
      + (1 - μ) / (2 * (s 0 ^ 2 + s 1 ^ 2)) + μ / N - c))
      - (2 * (s 0 * s 3 - s 1 * s 2) + 4 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 2 * μ * (s 0 ^ 2 - s 1 ^ 2)) ^ 2
      - 4 * ((s 0 * s 2 + s 1 * s 3) - μ * (2 * s 0 * s 1)) ^ 2
      + 8 * (s 0 ^ 2 + s 1 ^ 2) * ((s 2 ^ 2 + s 3 ^ 2) / 2 + c * (s 0 ^ 2 + s 1 ^ 2) - (1 - μ) / 2 + 2 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
          - μ * (s 0 * s 3 + s 1 * s 2) - μ * (s 0 ^ 2 + s 1 ^ 2) / N) = 0 := by
    field_simp
    ring
  generalize hPdef : s 0 ^ 2 + s 1 ^ 2 = P at *
  generalize hXdef : s 0 ^ 2 - s 1 ^ 2 = X at *
  have hNne : N ≠ 0 := hNpos.ne'
  have hPne : P ≠ 0 := hP.ne'
  have e1 : (s 2 ^ 2 + s 3 ^ 2) + 2 * c * P + 8 * P * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2) - 2 * μ * P / N
        + μ * P * (8 * P ^ 2 - 4 * X) / N ^ 3
      - 2 * P * (2 * P * (-(2 * P - μ * (X / P) - (1 - μ) / (2 * P) ^ 2
        - μ * (2 * P - X / P) / N ^ 3))
        + (2 * (s 0 * s 3 - s 1 * s 2) + 4 * P ^ 2 - 2 * μ * X))
      - 2 * ((s 2 ^ 2 + s 3 ^ 2) / 2 + c * P - (1 - μ) / 2 + 2 * P * (s 0 * s 3 - s 1 * s 2)
          - μ * (s 0 * s 3 + s 1 * s 2) - μ * P / N) = 0 := by
    field_simp
    ring
  rw [hH] at e1 e2
  generalize hA : 2 * P - μ * (X / P) - (1 - μ) / (2 * P) ^ 2 - μ * (2 * P - X / P) / N ^ 3 = F at *
  generalize hS : 2 * (((2 * P) ^ 2 - 2 * μ * (2 * P) * (X / P) + μ ^ 2) / 2
      + (1 - μ) / (2 * P) + μ / N - c) = S at *
  generalize hT : 2 * (s 0 * s 3 - s 1 * s 2) + 4 * P ^ 2 - 2 * μ * X = T at *
  have hApos : 0 < -F := by linarith
  generalize hAA : -F = A at *
  have hSA : S < A ^ 2 := by rw [← hAA]; nlinarith
  have hTle : T ^ 2 ≤ (2 * P) ^ 2 * S := by
    nlinarith [sq_nonneg ((s 0 * s 2 + s 1 * s 3) - μ * (2 * s 0 * s 1))]
  have hρA : 0 < 2 * P * A := by positivity
  have h4 : (2 * P) ^ 2 * S < (2 * P * A) ^ 2 := by
    have : (2 * P * A) ^ 2 = (2 * P) ^ 2 * A ^ 2 := by ring
    rw [this]; exact mul_lt_mul_of_pos_left hSA (by positivity)
  have hpos : 0 < 2 * P * A + T := by nlinarith
  nlinarith

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      leviCivitaHamiltonian μ c s = 0 →
        0 < deriv (fun a : ℝ =>
          leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i)) 1 := by
  intro s hs hH0
  have hAv := left_negative_closure_avoids_second_collision μ c hμ0 hμ1 hc
  obtain ⟨L, hL, hLval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  have hcL : 0 < jacobiHamiltonian μ L + c := by
    have h := hc
    unfold belowFirstCriticalValue at h
    rw [← hLval] at h
    linarith
  have hd0 : 0 < L 0 + μ := by linarith [hL.2.2.1]
  have hd1 : L 0 + μ < 1 := by linarith [hL.2.2.2.1]
  set d := L 0 + μ with hd
  -- the positive-energy barrier circle through the inner Lagrange point
  have hbar : ∀ x : Phase, 4 * (x 0 ^ 2 + x 1 ^ 2) ^ 2 = d ^ 2 →
      0 < leviCivitaHamiltonian μ c x := by
    intro x hx
    have hr : ((leviCivitaPosition μ x) 0 + μ) ^ 2 + ((leviCivitaPosition μ x) 1) ^ 2 =
        (L 0 + μ) ^ 2 := by
      rw [← hd, ← hx]; simp [leviCivitaPosition]; ring
    have hlow := inner_lagrange_circle_hamiltonian_lower_bound μ hμ0 hμ1 L hL x hr
    have hsplit : leviCivitaHamiltonian μ c x =
        leviCivitaHamiltonian μ 0 x + c * zNormSq x := by
      unfold leviCivitaHamiltonian; ring
    have hPpos : 0 < zNormSq x := by
      unfold zNormSq
      rcases (show (0:ℝ) ≤ x 0 ^ 2 + x 1 ^ 2 by positivity).eq_or_lt with h | h
      · rw [← h] at hx; nlinarith
      · exact h
    rw [hsplit]
    nlinarith [mul_pos hPpos hcL]
  -- the origin lies in the negative region
  have hD0 : secondCollisionDistanceSq (fun _ : Fin 4 => (0 : ℝ)) = 1 := by
    simp [secondCollisionDistanceSq]
  have hH00 : leviCivitaHamiltonian μ c (fun _ : Fin 4 => (0 : ℝ)) < 0 := by
    simp only [leviCivitaHamiltonian, hD0, zNormSq, wNormSq, Real.sqrt_one]
    simp
    linarith
  set U : Set Phase := {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
      0 < secondCollisionDistanceSq u} with hU
  have h0U : (fun _ : Fin 4 => (0 : ℝ)) ∈ U := ⟨hH00, by rw [hD0]; norm_num⟩
  have hPc : Continuous (fun x : Phase => 2 * (x 0 ^ 2 + x 1 ^ 2)) := by fun_prop
  have hKin : connectedComponentIn U (fun _ : Fin 4 => (0 : ℝ)) ⊆
      {x : Phase | 2 * (x 0 ^ 2 + x 1 ^ 2) < d} := by
    refine IsPreconnected.subset_left_of_subset_union
      (isOpen_lt hPc continuous_const : IsOpen {x : Phase | 2 * (x 0 ^ 2 + x 1 ^ 2) < d})
      (isOpen_lt continuous_const hPc : IsOpen {x : Phase | d < 2 * (x 0 ^ 2 + x 1 ^ 2)})
      (Set.disjoint_left.2 (fun x (h1 : 2 * (x 0 ^ 2 + x 1 ^ 2) < d) (h2 : d < 2 * (x 0 ^ 2 + x 1 ^ 2)) => lt_asymm h1 h2)) ?_ ?_
      isPreconnected_connectedComponentIn
    · intro x hx
      have hxU : x ∈ U := connectedComponentIn_subset _ _ hx
      rcases lt_trichotomy (2 * (x 0 ^ 2 + x 1 ^ 2)) d with h | h | h
      · exact Or.inl h
      · exfalso
        have := hbar x (by rw [← h]; ring)
        linarith [hxU.1]
      · exact Or.inr h
    · exact ⟨_, mem_connectedComponentIn h0U, by simp; linarith⟩
  have hsle : 2 * (s 0 ^ 2 + s 1 ^ 2) ≤ d :=
    closure_lt_subset_le hPc continuous_const (closure_mono hKin hs)
  have hslt : 2 * (s 0 ^ 2 + s 1 ^ 2) < d := by
    refine lt_of_le_of_ne hsle (fun h => ?_)
    have := hbar s (by rw [← h]; ring)
    linarith
  have hD : 0 < secondCollisionDistanceSq s := hAv s hs
  rw [(lc_radial_hasDerivAt μ c s hD).deriv]
  rcases (show (0:ℝ) ≤ s 0 ^ 2 + s 1 ^ 2 by positivity).eq_or_lt with hP | hP
  · -- the collision circle `z = 0`
    have h0 : s 0 = 0 := by nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
    have h1 : s 1 = 0 := by nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
    unfold leviCivitaHamiltonian zNormSq wNormSq secondCollisionDistanceSq at hH0
    simp [h0, h1] at hH0 ⊢
    nlinarith
  · -- polar data of the physical position
    set P := s 0 ^ 2 + s 1 ^ 2 with hPdef
    set ρ := 2 * P with hρ
    set κ := (s 0 ^ 2 - s 1 ^ 2) / P with hκ
    have hρ0 : 0 < ρ := by positivity
    have hκ0 : -1 ≤ κ := by
      rw [hκ, le_div_iff₀ hP]; nlinarith [sq_nonneg (s 0)]
    have hκ1 : κ ≤ 1 := by
      rw [hκ, div_le_one hP]; nlinarith [sq_nonneg (s 1)]
    have hF := inner_lagrange_ball_radial_force_negative μ hμ0 hμ1 L hL ρ κ hρ0 hslt hκ0 hκ1
    -- the barrier value along the same polar direction
    have hcirc : (d ^ 2 - 2 * μ * d * κ + μ ^ 2) / 2 + (1 - μ) / d +
        μ / Real.sqrt (d ^ 2 - 2 * d * κ + 1) < c := by
      set lam := Real.sqrt (d / (2 * P)) with hlam
      have hl2 : lam ^ 2 = d / (2 * P) := Real.sq_sqrt (by positivity)
      set s' : Phase := ![lam * s 0, lam * s 1, 0, 0] with hs'
      have hz' : zNormSq s' = d / 2 := by
        have : zNormSq s' = lam ^ 2 * P := by simp [zNormSq, s', hPdef]; ring
        rw [this, hl2]; field_simp
      have hq' : ((leviCivitaPosition μ s') 0) ^ 2 + ((leviCivitaPosition μ s') 1) ^ 2 =
          d ^ 2 - 2 * μ * d * κ + μ ^ 2 := by
        have : ((leviCivitaPosition μ s') 0) ^ 2 + ((leviCivitaPosition μ s') 1) ^ 2 =
            (2 * (lam ^ 2 * (s 0 ^ 2 - s 1 ^ 2)) - μ) ^ 2 + (4 * lam ^ 2 * (s 0 * s 1)) ^ 2 := by
          simp [leviCivitaPosition, s']; ring
        rw [this, hl2, hκ]; field_simp; ring
      have hD' : secondCollisionDistanceSq s' = d ^ 2 - 2 * d * κ + 1 := by
        have : secondCollisionDistanceSq s' =
            (2 * (lam ^ 2 * (s 0 ^ 2 - s 1 ^ 2)) - 1) ^ 2 + (4 * lam ^ 2 * (s 0 * s 1)) ^ 2 := by
          simp [secondCollisionDistanceSq, s']; ring
        rw [this, hl2, hκ]; field_simp; ring
      have hr' : ((leviCivitaPosition μ s') 0 + μ) ^ 2 + ((leviCivitaPosition μ s') 1) ^ 2 =
          (L 0 + μ) ^ 2 := by
        have : ((leviCivitaPosition μ s') 0 + μ) ^ 2 + ((leviCivitaPosition μ s') 1) ^ 2 =
            4 * (lam ^ 2 * P) ^ 2 := by
          simp [leviCivitaPosition, s', hPdef]; ring
        rw [this, hl2, ← hd]; field_simp; norm_num
      have hb := inner_lagrange_circle_effective_potential_bound μ hμ0 hμ1 L hL s' hr'
      rw [hz', hq', hD'] at hb
      have hNpos : 0 < Real.sqrt (d ^ 2 - 2 * d * κ + 1) := Real.sqrt_pos.2 (by nlinarith)
      have hb2 : jacobiHamiltonian μ L ≤ -((d ^ 2 - 2 * μ * d * κ + μ ^ 2) / 2 + (1 - μ) / d +
          μ / Real.sqrt (d ^ 2 - 2 * d * κ + 1)) := by
        have e : -((d ^ 2 - 2 * μ * d * κ + μ ^ 2) / 2 + (1 - μ) / d +
            μ / Real.sqrt (d ^ 2 - 2 * d * κ + 1)) = (-(d / 2) * (d ^ 2 - 2 * μ * d * κ + μ ^ 2) / 2 -
            (1 - μ) / 2 - μ * (d / 2) / Real.sqrt (d ^ 2 - 2 * d * κ + 1)) / (d / 2) := by
          field_simp
          ring
        rw [e, le_div_iff₀ (by positivity)]
        linarith
      linarith
    have hkey := key_radial_ineq μ κ ρ d c hρ0 hslt hd1 hκ1
      (fun r hr0 hrd => inner_lagrange_ball_radial_force_negative μ hμ0 hμ1 L hL r κ hr0 hrd hκ0 hκ1)
      (fun r hr0 hrd => inner_lagrange_ball_radial_convexity μ hμ0 hμ1 L hL r κ hr0 hrd.le hκ0 hκ1)
      hcirc
    have hQ : ρ ^ 2 - 2 * ρ * κ + 1 = secondCollisionDistanceSq s := by
      have hPne : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := ne_of_gt hP
      rw [hρ, hκ, secondCollisionDistanceSq, hPdef]; field_simp; ring
    rw [hQ] at hF hkey
    exact lc_R_pos μ c s hD hH0 hP hF hkey
