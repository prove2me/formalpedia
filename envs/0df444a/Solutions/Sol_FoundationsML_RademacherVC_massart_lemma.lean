-- Prove2me | solution 1 for FoundationsML.RademacherVC.massart_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:44:06.541615+00:00
-- url     : https://prove2.me/submissions/2874bc07-4bcb-4ec6-9d2b-5abb82272403

import Mathlib

namespace FoundationsML.RademacherVC

/-- Exponential-moment bound: for every `t > 0`,
`t * E_σ[sup_x ∑ σ_i x_i] ≤ log |A| + t^2 r^2 / 2`. -/
theorem aux_ms_key {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) (r : ℝ)
    (hr : ∀ x ∈ A, ∑ i, (x i) ^ 2 ≤ r ^ 2) (t : ℝ) (ht : 0 < t) :
    t * ((1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
        A.sup' hA (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i))
      ≤ Real.log (A.card : ℝ) + t ^ 2 * r ^ 2 / 2 := by
  set f : (Fin m → Bool) → (Fin m → ℝ) → ℝ :=
    fun σ x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i with hf
  set c : ℝ := 1 / (2 : ℝ) ^ m with hc
  have hc0 : 0 ≤ c := by positivity
  -- Jensen
  have hw : ∑ _σ : Fin m → Bool, c = 1 := by
    simp [hc, Finset.card_univ, Fintype.card_bool]
  have hJ : Real.exp (t * (c * ∑ σ, A.sup' hA (f σ)))
      ≤ c * ∑ σ, Real.exp (t * A.sup' hA (f σ)) := by
    have := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => c)
      (p := fun σ => t * A.sup' hA (f σ)) (fun _ _ => hc0) hw (by simp)
    simp only [smul_eq_mul] at this
    have e1 : t * (c * ∑ σ, A.sup' hA (f σ)) = ∑ σ, c * (t * A.sup' hA (f σ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => by ring)
    rw [e1, Finset.mul_sum]
    exact this
  have h2 : ∀ σ, Real.exp (t * A.sup' hA (f σ)) ≤ ∑ x ∈ A, Real.exp (t * f σ x) := by
    intro σ
    obtain ⟨x0, hx0, hx0eq⟩ := Finset.exists_mem_eq_sup' hA (f σ)
    rw [hx0eq]
    exact Finset.single_le_sum (f := fun x => Real.exp (t * f σ x))
      (fun x _ => (Real.exp_pos _).le) hx0
  have h3 : ∀ x : Fin m → ℝ, c * ∑ σ : Fin m → Bool, Real.exp (t * f σ x)
      = ∏ i, Real.cosh (t * x i) := by
    intro x
    have : ∀ σ : Fin m → Bool, Real.exp (t * f σ x)
        = ∏ i, Real.exp (t * ((if σ i then (1:ℝ) else -1) * x i)) := by
      intro σ; rw [← Real.exp_sum, hf, Finset.mul_sum]
    simp_rw [this]
    rw [← Fintype.prod_sum (f := fun i (b : Bool) =>
      Real.exp (t * ((if b then (1:ℝ) else -1) * x i)))]
    rw [show c = ∏ _i : Fin m, (1/2 : ℝ) by simp [hc]]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, Real.cosh_eq]
    ring_nf
  have h4 : ∀ x ∈ A, ∏ i, Real.cosh (t * x i) ≤ Real.exp (t ^ 2 * r ^ 2 / 2) := by
    intro x hx
    calc ∏ i, Real.cosh (t * x i) ≤ ∏ i, Real.exp ((t * x i) ^ 2 / 2) :=
          Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le)
            (fun i _ => Real.cosh_le_exp_half_sq _)
      _ = Real.exp (∑ i, (t * x i) ^ 2 / 2) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (t ^ 2 * r ^ 2 / 2) := by
          apply Real.exp_le_exp.mpr
          have := hr x hx
          calc ∑ i, (t * x i) ^ 2 / 2 = t ^ 2 * (∑ i, (x i) ^ 2) / 2 := by
                rw [Finset.mul_sum, Finset.sum_div]
                refine Finset.sum_congr rfl (fun i _ => by ring)
            _ ≤ _ := by gcongr
  have hmain : Real.exp (t * (c * ∑ σ, A.sup' hA (f σ)))
      ≤ (A.card : ℝ) * Real.exp (t ^ 2 * r ^ 2 / 2) := by
    calc Real.exp (t * (c * ∑ σ, A.sup' hA (f σ)))
        ≤ c * ∑ σ, Real.exp (t * A.sup' hA (f σ)) := hJ
      _ ≤ c * ∑ σ, ∑ x ∈ A, Real.exp (t * f σ x) := by
          gcongr with σ; exact h2 σ
      _ = ∑ x ∈ A, c * ∑ σ, Real.exp (t * f σ x) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ = ∑ x ∈ A, ∏ i, Real.cosh (t * x i) := by
          refine Finset.sum_congr rfl (fun x _ => h3 x)
      _ ≤ ∑ _x ∈ A, Real.exp (t ^ 2 * r ^ 2 / 2) := Finset.sum_le_sum h4
      _ = (A.card : ℝ) * Real.exp (t ^ 2 * r ^ 2 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have := Real.log_le_log (Real.exp_pos _) hmain
  rw [Real.log_exp, Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  exact this

end FoundationsML.RademacherVC

open FoundationsML.RademacherVC

theorem solution
    {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) (r : ℝ)
    (hr : ∀ x ∈ A, Real.sqrt (∑ i, (x i) ^ 2) ≤ r) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
        (1 / (m : ℝ)) * A.sup' hA (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i)
      ≤ r * Real.sqrt (2 * Real.log (A.card : ℝ) / m) := by
  obtain ⟨x0, hx0⟩ := hA
  have hr0 : 0 ≤ r := le_trans (Real.sqrt_nonneg _) (hr x0 hx0)
  have hr2 : ∀ x ∈ A, ∑ i, (x i) ^ 2 ≤ r ^ 2 := by
    intro x hx
    have h1 := hr x hx
    have h2 : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [← Real.sq_sqrt h2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  set S : ℝ := (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      A.sup' ⟨x0, hx0⟩ (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i) with hS
  set L : ℝ := Real.log (A.card : ℝ) with hL
  have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr ⟨x0, hx0⟩
  have hL0 : 0 ≤ L := Real.log_nonneg hcard
  have key : ∀ t : ℝ, 0 < t → t * S ≤ L + t ^ 2 * r ^ 2 / 2 :=
    fun t ht => aux_ms_key A ⟨x0, hx0⟩ r hr2 t ht
  have hSb : S ≤ r * Real.sqrt (2 * L) := by
    rcases hr0.eq_or_lt with hr0' | hrpos
    · -- r = 0
      subst hr0'
      simp only [zero_mul]
      by_contra hneg
      push Not at hneg
      have := key ((L + 1) / S) (by positivity)
      rw [div_mul_cancel₀ _ hneg.ne'] at this
      nlinarith
    rcases hL0.eq_or_lt with hL0' | hLpos
    · -- L = 0
      rw [← hL0']
      simp only [mul_zero, Real.sqrt_zero]
      by_contra hneg
      push Not at hneg
      have hr2pos : 0 < r ^ 2 := by positivity
      have := key (S / r ^ 2) (by positivity)
      rw [← hL0'] at this
      have e1 : S / r ^ 2 * S = S ^ 2 / r ^ 2 := by ring
      have e2 : (S / r ^ 2) ^ 2 * r ^ 2 / 2 = S ^ 2 / r ^ 2 / 2 := by
        field_simp
      rw [e1, e2] at this
      have : 0 < S ^ 2 / r ^ 2 := by positivity
      linarith
    · -- main case
      set q : ℝ := Real.sqrt (2 * L) with hq
      have hqpos : 0 < q := Real.sqrt_pos.mpr (by linarith)
      have hq2 : q ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
      have := key (q / r) (by positivity)
      have e : (q / r) ^ 2 * r ^ 2 / 2 = L := by
        rw [div_pow, div_mul_cancel₀ _ (by positivity), hq2]; ring
      rw [e] at this
      -- (q / r) * S ≤ 2 L = q^2
      have h' : q * S ≤ r * q ^ 2 := by
        have := mul_le_mul_of_nonneg_left this hrpos.le
        rw [hq2]
        calc q * S = r * (q / r * S) := by field_simp
          _ ≤ r * (L + L) := this
          _ = r * (2 * L) := by ring
      have : S ≤ r * q := by
        by_contra hneg
        push Not at hneg
        have : q * (r * q) < q * S := mul_lt_mul_of_pos_left hneg hqpos
        nlinarith
      exact this
  have hLHS : (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
        (1 / (m : ℝ)) * A.sup' ⟨x0, hx0⟩
          (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i)
      = (1 / (m : ℝ)) * S := by
    rw [hS, ← Finset.mul_sum]; ring
  rw [hLHS]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < m := by linarith
    calc (1 / (m : ℝ)) * S ≤ (1 / (m : ℝ)) * (r * Real.sqrt (2 * L)) := by
          gcongr
      _ ≤ r * Real.sqrt (2 * L / m) := by
          rw [Real.sqrt_div' _ hmpos.le]
          have hsm : Real.sqrt (m : ℝ) ≤ m := by
            rw [Real.sqrt_le_left]
            · nlinarith
            · linarith
          have hsmpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
          have hq0 : 0 ≤ r * Real.sqrt (2 * L) := by positivity
          calc 1 / (m : ℝ) * (r * Real.sqrt (2 * L))
              = (r * Real.sqrt (2 * L)) / m := by ring
            _ ≤ (r * Real.sqrt (2 * L)) / Real.sqrt m :=
                div_le_div_of_nonneg_left hq0 hsmpos hsm
            _ = r * (Real.sqrt (2 * L) / Real.sqrt m) := by ring
