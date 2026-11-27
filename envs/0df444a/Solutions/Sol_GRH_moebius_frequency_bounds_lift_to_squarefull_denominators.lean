-- Prove2me | solution 1 for GRH.moebius_frequency_bounds_lift_to_squarefull_denominators
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:04:56.440671+00:00
-- url     : https://prove2.me/submissions/42b73f09-dadd-43d1-bedc-86f9d243828b

import Theorems.Thm_GRH_prime_square_fourier_filter_and_coprime_harmonic_recursion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

private theorem sumBounds (A : Finset ℕ) (x : ℕ → ℚ) (θ : ℝ)
    (hA : ∀ j ∈ A, boundAt (x j) θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖∑ j ∈ A, transform false N (x j)‖ ≤ C*((N : ℝ)+1)^θ := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert j A hj ih =>
    obtain ⟨C,hC,hj'⟩ := hA j (mem_insert_self ..)
    obtain ⟨D,hD,hA'⟩ := ih (fun k hk => hA k (mem_insert_of_mem hk))
    refine ⟨C+D,add_nonneg hC hD,fun N => ?_⟩
    rw [sum_insert hj,add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hj' N) (hA' N))

private theorem down (p d : ℕ) (hp : p.Prime) (hd : 0 < d) (hpd : ¬p ∣ d)
    (θ : ℝ) (hθ : 0 ≤ θ) (H : level (p*(p*d)) θ) : level (p*d) θ := by
  let : NeZero p := ⟨hp.ne_zero⟩
  intro a ha
  have hcop := Nat.coprime_mul_iff_right.mp ha
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  let x : ℚ := (a : ℚ)/(p*d : ℕ)
  have hA (j : ℕ) (hj : j ∈ (range (p^2)).filter (fun j => ¬p ∣ j)) :
      boundAt (x+(j : ℚ)/(p : ℚ)^2) θ := by
    have hc : (p*a+j*d).Coprime p := (hp.coprime_iff_not_dvd.mpr (by
      intro h
      have h' : p ∣ j*d := (Nat.dvd_add_iff_right (dvd_mul_right p a)).mpr h
      exact (hp.dvd_mul.mp h').elim (mem_filter.mp hj).2 hpd)).symm
    have hc' : (p*a+j*d).Coprime d := (Nat.coprime_add_mul_right_left _ _ _).mpr
      (Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hcop.2⟩)
    have e : x+(j : ℚ)/(p : ℚ)^2 = ((p*a+j*d : ℕ) : ℚ)/(p*(p*d) : ℕ) := by
      dsimp [x]
      push_cast
      field_simp
    rw [e]
    exact H _ (Nat.coprime_mul_iff_right.mpr ⟨hc,Nat.coprime_mul_iff_right.mpr ⟨hc,hc'⟩⟩)
  have hB (j : ℕ) (_ : j ∈ range p) : boundAt (x/p+(j : ℚ)/p) θ := by
    have hc : (a+j*(p*d)).Coprime (p*d) := (Nat.coprime_add_mul_right_left _ _ _).mpr ha
    have e : x/p+(j : ℚ)/p = ((a+j*(p*d) : ℕ) : ℚ)/(p*(p*d) : ℕ) := by
      dsimp [x]
      push_cast
      field_simp
    rw [e]
    exact H _ (Nat.coprime_mul_iff_right.mpr ⟨(Nat.coprime_mul_iff_right.mp hc).1,hc⟩)
  obtain ⟨C,hC,h1⟩ := sumBounds _ _ θ hA
  obtain ⟨D,hD,h2⟩ := sumBounds _ _ θ hB
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.pos
  have hk : 0 ≤ ((p : ℝ)+1)^θ := by positivity
  refine ⟨C+D*((p : ℝ)+1)^θ,by positivity,fun N => ?_⟩
  have iden := (GRH.prime_square_fourier_filter_and_coprime_harmonic_recursion p hp).1 N x
  have e : (p : ℂ)*transform false N x =
      -(primeSquareShifts p N x + shifts p (p*N) (x/p)) := by linear_combination iden
  have g : (((p*N : ℕ) : ℝ)+1)^θ ≤ ((p : ℝ)+1)^θ*((N : ℝ)+1)^θ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hθ
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) N]
  change ‖transform false N x‖ ≤ _
  calc
    _ ≤ (p : ℝ)*‖transform false N x‖ := le_mul_of_one_le_left (norm_nonneg _) hpR
    _ = ‖(p : ℂ)*transform false N x‖ := by simp
    _ ≤ ‖primeSquareShifts p N x‖ + ‖shifts p (p*N) (x/p)‖ := by
      rw [e,norm_neg]; exact norm_add_le _ _
    _ ≤ C*((N : ℝ)+1)^θ + D*(((p*N : ℕ) : ℝ)+1)^θ := add_le_add (h1 N) (h2 (p*N))
    _ ≤ C*((N : ℝ)+1)^θ + D*(((p : ℝ)+1)^θ*((N : ℝ)+1)^θ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left g hD)
    _ = _ := by ring

private theorem extension (p d t : ℕ) (hp : p.Prime) (h : ¬p ∣ d)
    (hdiv : p*d ∣ t) (hsq : p^2 ∣ t) : p*(p*d) ∣ t := by
  obtain ⟨r,hr⟩ := hdiv
  have hpr : p ∣ d*r := by
    apply Nat.dvd_of_mul_dvd_mul_left hp.pos
    simpa only [pow_two,hr,mul_assoc] using hsq
  obtain ⟨k,hk⟩ := (hp.dvd_mul.mp hpr).resolve_left h
  refine ⟨k,?_⟩
  rw [hr,hk]
  ring

private theorem descend (t : ℕ) (ht : squarefull t) (θ : ℝ) (hθ : 0 ≤ θ)
    (q : ℕ) (hq : 0 < q) (hqt : q ∣ t) (ht0 : 0 < t)
    (H : ∀ e : ℕ, q ∣ e → e ∣ t → squarefull e → level e θ) : level q θ := by
  classical
  by_cases h : squarefull q
  · exact H q dvd_rfl hqt h
  · unfold squarefull at h
    push Not at h
    obtain ⟨p,hp,hd,hsq⟩ := h
    obtain ⟨d,e⟩ := hd
    subst q
    have hn : ¬p ∣ d := fun h => hsq (by simpa only [pow_two] using Nat.mul_dvd_mul_left p h)
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
    have hdiv := extension p d t hp hn hqt (ht p hp ((dvd_mul_right p d).trans hqt))
    have hin : p*d ∣ p*(p*d) := dvd_mul_left _ _
    have hbig : p*d < p*(p*d) := by
      calc
        _ = 1*(p*d) := (one_mul _).symm
        _ < _ := (Nat.mul_lt_mul_right hq).mpr hp.one_lt
    have hb := Nat.le_of_dvd ht0 hdiv
    exact down p d hp hd0 hn θ hθ (descend t ht θ hθ (p*(p*d)) (Nat.mul_pos hp.pos hq)
      hdiv ht0 (fun e h1 h2 h3 => H e (hin.trans h1) h2 h3))
termination_by t-q
decreasing_by omega

theorem solution (q : ℕ) (hq : 0 < q) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∀ t : ℕ, 0 < t → squarefull t → q ∣ t →
      (∀ d : ℕ, q ∣ d → d ∣ t → squarefull d → level d θ) → level q θ) ∧
    ((∀ d : ℕ, q ∣ d → d ∣ q^2 → squarefull d → level d θ) → level q θ) := by
  refine ⟨fun t ht hsf hqt => descend t hsf θ hθ q hq hqt ht,?_⟩
  intro H
  have h : squarefull (q^2) := by
    intro p hp hd
    exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) _
  exact descend (q^2) h θ hθ q hq (by simp [pow_two]) (by positivity) H
