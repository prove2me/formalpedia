-- Prove2me | solution 1 for CVPricing.CertEquiv.induction_on_eventA
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:13:06.481993+00:00
-- url     : https://prove2.me/submissions/158b9beb-1d0b-496a-8653-6edb1cd32ce6

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_CEPrice
import Definitions.Def_CVPricing_CertEquiv_EventA

open CVPricing.CertEquiv
open KeskinZeevi.SufficientConditions (lsEstimateOf fisherOf avgPriceOf)

theorem cvp_split (F : ℕ → ℝ) (t : ℕ) (ht : 2 ≤ t) :
    ∑ s ∈ Finset.Icc 1 t, F s = F 1 + F 2 + ∑ s ∈ Finset.Icc 3 t, F s := by
  have h : Finset.Icc 1 t = insert 1 (insert 2 (Finset.Icc 3 t)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  ring

theorem cvp_ls (p D : ℕ → ℝ) (t : ℕ) (P Q DD R : ℝ)
    (hP : ∑ s ∈ Finset.Icc 1 t, p s = P) (hQ : ∑ s ∈ Finset.Icc 1 t, p s ^ 2 = Q)
    (hD : ∑ s ∈ Finset.Icc 1 t, D s = DD) (hR : ∑ s ∈ Finset.Icc 1 t, D s * p s = R)
    (hdet : (t : ℝ) * Q - P ^ 2 ≠ 0) :
    lsEstimateOf p D t =
      ((Q * DD - P * R) / ((t : ℝ) * Q - P ^ 2), ((t : ℝ) * R - P * DD) / ((t : ℝ) * Q - P ^ 2)) := by
  have hF : fisherOf p t = !![(t : ℝ), P; P, Q] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fisherOf, Matrix.sum_apply, hP, hQ]
  have hdet' : (t : ℝ) * Q - P * P ≠ 0 := by rw [← sq]; exact hdet
  unfold lsEstimateOf
  rw [hF, hD, hR, Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  simp only [Ring.inverse_eq_inv']
  ext
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring

theorem cvp_rule (M : Model) (x y : ℝ) (h : 0 ≤ x + 2 * M.ph * y) : ceRule M (x, y) = M.ph := by
  unfold ceRule
  dsimp only
  split_ifs with hy
  · rfl
  · rw [not_le] at hy
    have : M.ph ≤ -x / (2 * y) := by
      rw [le_div_iff_of_neg (by linarith)]; linarith
    rw [min_eq_left this, max_eq_right M.pl_lt_ph.le]

theorem cvp_alg2 (p1 p2 ph a0 a1 e1 e2 P Q DD R : ℝ) (h12 : p1 < p2) (ha0 : 0 < a0)
    (h1 : -a1 * (p2 - p1) * (2 * ph) ≤ (p2 - 2 * ph) * e1 + (2 * ph - p1) * e2)
    (hP : P = p1 + p2 + (2 - 2) * ph) (hQ : Q = p1 ^ 2 + p2 ^ 2 + (2 - 2) * ph ^ 2)
    (hD : DD = (a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) + (2 - 2) * (a0 + a1 * ph) + 0)
    (hR : R = (a0 + a1 * p1 + e1) * p1 + (a0 + a1 * p2 + e2) * p2 +
      ((2 - 2) * (a0 + a1 * ph) + 0) * ph) :
    0 ≤ (Q * DD - P * R) + 2 * ph * ((2:ℝ) * R - P * DD) := by
  subst hP hQ hD hR
  have hH : 0 ≤ (a0 + 2 * ph * a1) * (p2 - p1) + e1 * (p2 - 2 * ph) + e2 * (2 * ph - p1) := by
    nlinarith [mul_pos ha0 (sub_pos.2 h12)]
  have : (p1 ^ 2 + p2 ^ 2 + (2 - 2) * ph ^ 2) *
      ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) + (2 - 2) * (a0 + a1 * ph) + 0) -
      (p1 + p2 + (2 - 2) * ph) * ((a0 + a1 * p1 + e1) * p1 + (a0 + a1 * p2 + e2) * p2 +
      ((2 - 2) * (a0 + a1 * ph) + 0) * ph) + 2 * ph * ((2:ℝ) * ((a0 + a1 * p1 + e1) * p1 +
      (a0 + a1 * p2 + e2) * p2 + ((2 - 2) * (a0 + a1 * ph) + 0) * ph) -
      (p1 + p2 + (2 - 2) * ph) * ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) +
      (2 - 2) * (a0 + a1 * ph) + 0)) =
      (p2 - p1) * ((a0 + 2 * ph * a1) * (p2 - p1) + e1 * (p2 - 2 * ph) + e2 * (2 * ph - p1)) := by
    ring
  rw [this]
  exact mul_nonneg (sub_pos.2 h12).le hH

theorem cvp_alg3 (p1 p2 ph a0 a1 e1 e2 E3 n δ a P Q DD R : ℝ) (hn : 2 ≤ n)
    (hp1 : p1 ≤ ph) (hp2 : p2 ≤ ph) (hph : 0 < ph) (hK : 0 < -2 * ph * a1 - a0) (hδ : 0 < δ)
    (ha : a * ph = (ph - p1) ^ 2 + (ph - p2) ^ 2)
    (hσ : |(e1 + e2 + E3) / n| ≤ δ)
    (h2 : (-2 * ph * a1 - a0 + δ) * a + (2 * ph - p1 - p2) * δ ≤ (p1 - ph) * e1 + (p2 - ph) * e2)
    (hP : P = p1 + p2 + (n - 2) * ph) (hQ : Q = p1 ^ 2 + p2 ^ 2 + (n - 2) * ph ^ 2)
    (hD : DD = (a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) + (n - 2) * (a0 + a1 * ph) + E3)
    (hR : R = (a0 + a1 * p1 + e1) * p1 + (a0 + a1 * p2 + e2) * p2 +
      ((n - 2) * (a0 + a1 * ph) + E3) * ph) :
    0 ≤ (Q * DD - P * R) + 2 * ph * (n * R - P * DD) := by
  subst hP hQ hD hR
  have hn0 : 0 < n := by linarith
  set K := -2 * ph * a1 - a0 with hKdef
  set σ := e1 + e2 + E3 with hσdef
  set S := 2 * ph - p1 - p2 with hSdef
  set X := (p1 - ph) * e1 + (p2 - ph) * e2 with hXdef
  have hS : 0 ≤ S := by rw [hSdef]; linarith
  have ha0 : 0 ≤ a := by
    have : 0 ≤ a * ph := by rw [ha]; positivity
    exact nonneg_of_mul_nonneg_left this hph
  rw [abs_le, le_div_iff₀ hn0, div_le_iff₀ hn0] at hσ
  obtain ⟨hlo, hhi⟩ := hσ
  have s1 : n * X + S * σ ≥ n * ((K + δ) * a) := by
    nlinarith [mul_le_mul_of_nonneg_left hlo hS]
  have s2 : (n * X + S * σ) * (n * ph + S) ≥ n * ((K + δ) * a) * (n * ph + S) :=
    mul_le_mul_of_nonneg_right s1 (by positivity)
  have hnA : 0 ≤ n * ((ph - p1) ^ 2 + (ph - p2) ^ 2) - S ^ 2 := by
    rw [hSdef]; nlinarith [sq_nonneg (p1 - p2), sq_nonneg (ph - p1), sq_nonneg (ph - p2)]
  have s3 : (n * ((ph - p1) ^ 2 + (ph - p2) ^ 2) - S ^ 2) * (σ - n * K) ≥
      (n * ((ph - p1) ^ 2 + (ph - p2) ^ 2) - S ^ 2) * (-(n * (δ + K))) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hnA
  have key : n * ((K + δ) * a) * (n * ph + S) +
      (n * ((ph - p1) ^ 2 + (ph - p2) ^ 2) - S ^ 2) * (-(n * (δ + K))) =
      n * (K + δ) * (a * S + S ^ 2) := by
    rw [← ha]; ring
  have hpos : 0 ≤ n * (K + δ) * (a * S + S ^ 2) := by positivity
  have hW : n * ((p1 ^ 2 + p2 ^ 2 + (n - 2) * ph ^ 2) *
      ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) + (n - 2) * (a0 + a1 * ph) + E3) -
      (p1 + p2 + (n - 2) * ph) * ((a0 + a1 * p1 + e1) * p1 + (a0 + a1 * p2 + e2) * p2 +
      ((n - 2) * (a0 + a1 * ph) + E3) * ph) + 2 * ph * (n * ((a0 + a1 * p1 + e1) * p1 +
      (a0 + a1 * p2 + e2) * p2 + ((n - 2) * (a0 + a1 * ph) + E3) * ph) -
      (p1 + p2 + (n - 2) * ph) * ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) +
      (n - 2) * (a0 + a1 * ph) + E3))) =
      (n * ((ph - p1) ^ 2 + (ph - p2) ^ 2) - S ^ 2) * (σ - n * K) +
        (n * X + S * σ) * (n * ph + S) := by
    rw [hSdef, hσdef, hKdef, hXdef]; ring
  have : 0 ≤ n * ((p1 ^ 2 + p2 ^ 2 + (n - 2) * ph ^ 2) *
      ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) + (n - 2) * (a0 + a1 * ph) + E3) -
      (p1 + p2 + (n - 2) * ph) * ((a0 + a1 * p1 + e1) * p1 + (a0 + a1 * p2 + e2) * p2 +
      ((n - 2) * (a0 + a1 * ph) + E3) * ph) + 2 * ph * (n * ((a0 + a1 * p1 + e1) * p1 +
      (a0 + a1 * p2 + e2) * p2 + ((n - 2) * (a0 + a1 * ph) + E3) * ph) -
      (p1 + p2 + (n - 2) * ph) * ((a0 + a1 * p1 + e1) + (a0 + a1 * p2 + e2) +
      (n - 2) * (a0 + a1 * ph) + E3))) := by
    rw [hW]; linarith
  exact (mul_nonneg_iff_of_pos_left hn0).1 this

theorem solution (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (h12 : p₁ < p₂) {δ : ℝ} (hδ : 0 < δ) (e : ℕ → ℝ)
    (hA : EventA M p₁ p₂ δ e) :
    ∀ t : ℕ, 2 ≤ t → cePrice M p₁ p₂ e (t + 1) = M.ph := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hph : 0 < M.ph := lt_trans M.pl_pos M.pl_lt_ph
  have hK : 0 < -2 * M.ph * M.a₁ - M.a₀ := by
    have h := M.opt_mem.2
    rw [div_lt_iff_of_neg (by linarith [M.a₁_neg])] at h
    linarith
  have c1 : cePrice M p₁ p₂ e 1 = p₁ := by rw [cePrice]; simp
  have c2 : cePrice M p₁ p₂ e 2 = p₂ := by rw [cePrice]; simp
  have step : ∀ t : ℕ, 2 ≤ t → (∀ s ∈ Finset.Icc 3 t, cePrice M p₁ p₂ e s = M.ph) →
      cePrice M p₁ p₂ e (t + 1) = M.ph := by
    intro t ht hph3
    have hsum : ∀ F : ℝ → ℝ → ℝ, ∑ s ∈ Finset.Icc 1 t, F (cePrice M p₁ p₂ e s) (e s) =
        F p₁ (e 1) + F p₂ (e 2) + ∑ s ∈ Finset.Icc 3 t, F M.ph (e s) := by
      intro F
      rw [cvp_split _ t ht, c1, c2]
      congr 1
      exact Finset.sum_congr rfl (fun s hs => by rw [hph3 s hs])
    have hc : ((Finset.Icc 3 t).card : ℝ) = (t : ℝ) - 2 := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega)]; push_cast; ring
    have hlt : ∀ s ∈ Finset.Icc 1 t, s < t + 1 := fun s hs => by
      simp only [Finset.mem_Icc] at hs; omega
    set E3 := ∑ s ∈ Finset.Icc 3 t, e s with hE3
    have hP : ∑ s ∈ Finset.Icc 1 t, (fun s => if s < t + 1 then cePrice M p₁ p₂ e s else 0) s =
        p₁ + p₂ + ((t : ℝ) - 2) * M.ph := by
      rw [Finset.sum_congr rfl (fun s hs => if_pos (hlt s hs))]
      rw [hsum (fun x _ => x)]
      simp only [Finset.sum_const, nsmul_eq_mul, hc]
    have hQ : ∑ s ∈ Finset.Icc 1 t,
        (fun s => if s < t + 1 then cePrice M p₁ p₂ e s else 0) s ^ 2 =
        p₁ ^ 2 + p₂ ^ 2 + ((t : ℝ) - 2) * M.ph ^ 2 := by
      rw [Finset.sum_congr rfl (g := fun s => cePrice M p₁ p₂ e s ^ 2)
        (fun s hs => by simp only [if_pos (hlt s hs)])]
      rw [hsum (fun x _ => x ^ 2)]
      simp only [Finset.sum_const, nsmul_eq_mul, hc]
    have hD : ∑ s ∈ Finset.Icc 1 t,
        (fun s => if s < t + 1 then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0) s =
        (M.a₀ + M.a₁ * p₁ + e 1) + (M.a₀ + M.a₁ * p₂ + e 2) +
          ((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3 := by
      rw [Finset.sum_congr rfl (fun s hs => if_pos (hlt s hs))]
      rw [hsum (fun x y => M.a₀ + M.a₁ * x + y)]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hc, ← hE3]
      ring
    have hR : ∑ s ∈ Finset.Icc 1 t,
        (fun s => if s < t + 1 then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0) s *
        (fun s => if s < t + 1 then cePrice M p₁ p₂ e s else 0) s =
        (M.a₀ + M.a₁ * p₁ + e 1) * p₁ + (M.a₀ + M.a₁ * p₂ + e 2) * p₂ +
          (((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3) * M.ph := by
      rw [Finset.sum_congr rfl
        (g := fun s => (M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s) * cePrice M p₁ p₂ e s)
        (fun s hs => by simp only [if_pos (hlt s hs)])]
      rw [hsum (fun x y => (M.a₀ + M.a₁ * x + y) * x)]
      simp only [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hc,
        ← hE3]
      ring
    have hdetpos : 0 < (t : ℝ) * (p₁ ^ 2 + p₂ ^ 2 + ((t : ℝ) - 2) * M.ph ^ 2) -
        (p₁ + p₂ + ((t : ℝ) - 2) * M.ph) ^ 2 := by
      have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
      have : (t : ℝ) * (p₁ ^ 2 + p₂ ^ 2 + ((t : ℝ) - 2) * M.ph ^ 2) -
          (p₁ + p₂ + ((t : ℝ) - 2) * M.ph) ^ 2 =
          (p₁ - p₂) ^ 2 + ((t : ℝ) - 2) * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) := by ring
      rw [this]
      have : 0 < (p₁ - p₂) ^ 2 := by nlinarith
      have : 0 ≤ ((t : ℝ) - 2) * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) :=
        mul_nonneg (by linarith) (by positivity)
      linarith
    rw [cePrice, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel,
      cvp_ls _ _ t _ _ _ _ hP hQ hD hR hdetpos.ne']
    apply cvp_rule
    have hG : 0 ≤ ((p₁ ^ 2 + p₂ ^ 2 + ((t : ℝ) - 2) * M.ph ^ 2) *
        ((M.a₀ + M.a₁ * p₁ + e 1) + (M.a₀ + M.a₁ * p₂ + e 2) +
          ((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3) -
        (p₁ + p₂ + ((t : ℝ) - 2) * M.ph) * ((M.a₀ + M.a₁ * p₁ + e 1) * p₁ +
          (M.a₀ + M.a₁ * p₂ + e 2) * p₂ + (((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3) * M.ph)) +
        2 * M.ph * ((t : ℝ) * ((M.a₀ + M.a₁ * p₁ + e 1) * p₁ +
          (M.a₀ + M.a₁ * p₂ + e 2) * p₂ + (((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3) * M.ph) -
        (p₁ + p₂ + ((t : ℝ) - 2) * M.ph) * ((M.a₀ + M.a₁ * p₁ + e 1) + (M.a₀ + M.a₁ * p₂ + e 2) +
          ((t : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + E3)) := by
      rcases Nat.eq_or_lt_of_le ht with h2 | h3
      · subst h2
        have hE : E3 = 0 := by rw [hE3]; simp
        rw [hE]
        simp only [Nat.cast_ofNat]
        exact cvp_alg2 p₁ p₂ M.ph M.a₀ M.a₁ (e 1) (e 2) _ _ _ _ h12 M.a₀_pos hA1
          rfl rfl rfl rfl
      · have hav := hA3 t (by omega)
        have hσ : avgPriceOf e t = (e 1 + e 2 + E3) / t := by
          unfold avgPriceOf
          rw [cvp_split e t ht]
        rw [hσ] at hav
        exact cvp_alg3 p₁ p₂ M.ph M.a₀ M.a₁ (e 1) (e 2) E3 t δ (aConst M p₁ p₂) _ _ _ _
          (by exact_mod_cast ht) hp₁.2 hp₂.2 hph hK hδ
          (by unfold aConst; field_simp) hav hA2 rfl rfl rfl rfl
    rw [mul_div_assoc', ← add_div]
    exact div_nonneg hG hdetpos.le
  have all : ∀ t, 2 ≤ t → ∀ s ∈ Finset.Icc 3 (t + 1), cePrice M p₁ p₂ e s = M.ph := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro s hs
      have : s = 3 := by simp only [Finset.mem_Icc] at hs; omega
      subst this
      exact step 2 le_rfl (by intro s hs; simp only [Finset.mem_Icc] at hs; omega)
    | succ t ht ih =>
      intro s hs
      simp only [Finset.mem_Icc] at hs
      rcases (show s ≤ t + 1 ∨ s = t + 2 by omega) with h | h
      · exact ih s (by simp only [Finset.mem_Icc]; omega)
      · subst h; exact step (t + 1) (by omega) ih
  intro t ht
  exact all t ht (t + 1) (by simp only [Finset.mem_Icc]; omega)
