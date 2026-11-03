-- Prove2me | solution 1 for FracRiccati.Radius.coeff_bound_B_49
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:20:53.593374+00:00
-- url     : https://prove2.me/submissions/89007723-194b-40ad-85a6-3f33148ee915

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Theorems.Thm_FracRiccati_Radius_lemma_A_1

namespace Aux_FRR_B49
open FracRiccati.Radius

lemma beta_real (α : ℝ) (hα : 0 < α) :
    ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) =
      Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (α : ℂ)) (t := (α : ℂ))
    (by simp [hα]) (by simp [hα])
  have hI : Complex.betaIntegral (α : ℂ) (α : ℂ) =
      ((∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only
    rw [Real.mul_rpow hx0 (by linarith), Complex.ofReal_mul, Complex.ofReal_cpow hx0,
      Complex.ofReal_cpow (by linarith)]
    push_cast
    ring_nf
  have hadd : ((α : ℂ) + (α : ℂ)) = ((α + α : ℝ) : ℂ) := by push_cast; ring
  rw [hI, hadd, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  have h' : Real.Gamma α * Real.Gamma α =
      Real.Gamma (α + α) * ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) := by
    exact_mod_cast h
  have hG : 0 < Real.Gamma (α + α) := Real.Gamma_pos_of_pos (by linarith)
  rw [h']; field_simp

lemma coeff_rec (α : ℝ) (lam mu nu : ℂ) (j : ℕ) : coeff α lam mu nu (j + 2) =
    (lam * ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
      + mu * coeff α lam mu nu (j + 1)) *
      ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
  rw [coeff, Finset.sum_attach (Finset.Ico 1 (j + 1))
    (fun ℓ => coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ))]


/-- Wendel-type upper bound from log-convexity: `Γ(x+s) ≤ x^s Γ(x)` for `s ∈ [0,1]`. -/
lemma gamma_upper (x s : ℝ) (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.Gamma (x + s) ≤ x ^ s * Real.Gamma x := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · subst h0; simp
  rcases eq_or_lt_of_le hs1 with h | h
  · subst h; rw [Real.rpow_one, Real.Gamma_add_one hx.ne']
  · have key := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1)
      (a := 1 - s) (b := s) hx (by linarith) (by linarith) h0 (by ring)
    have e1 : (1 - s) * x + s * (x + 1) = x + s := by ring
    rw [e1, Real.Gamma_add_one hx.ne', Real.mul_rpow hx.le hG.le] at key
    calc Real.Gamma (x + s) ≤ Real.Gamma x ^ (1 - s) * (x ^ s * Real.Gamma x ^ s) := key
      _ = x ^ s * (Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s) := by ring
      _ = x ^ s * Real.Gamma x := by
        rw [← Real.rpow_add hG, show 1 - s + s = 1 by ring, Real.rpow_one]

/-- `Γ(αK+1)/Γ(αK+α+1) ≤ (α(K+1))^{-α}` for `α ∈ (0,1]`. -/
lemma gamma_ratio (α K : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) :
    Real.Gamma (α * K + 1) / Real.Gamma (α * K + α + 1) ≤ (α * (K + 1)) ^ (-α) := by
  set x := α * (K + 1) with hx
  have hxpos : 0 < x := by positivity
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hxpos
  have e1 : α * K + 1 = x + (1 - α) := by rw [hx]; ring
  have e2 : α * K + α + 1 = x + 1 := by rw [hx]; ring
  rw [e1, e2, Real.Gamma_add_one hxpos.ne']
  have hW := gamma_upper x (1 - α) hxpos (by linarith) (by linarith)
  rw [div_le_iff₀ (by positivity)]
  calc Real.Gamma (x + (1 - α)) ≤ x ^ (1 - α) * Real.Gamma x := hW
    _ = x ^ (-α) * (x * Real.Gamma x) := by
      rw [show (1 - α) = -α + 1 by ring, Real.rpow_add_one hxpos.ne']; ring

/-- the Riemann-sum (kernel) bound for `α ∈ (0,1]`. -/
lemma kernel_sum (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    ∑ ℓ ∈ Finset.Ico 1 K, (ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1) ≤
      (K : ℝ) ^ (α - 1) * (K : ℝ) ^ (α - 1) * K *
        (Real.Gamma α * Real.Gamma α / Real.Gamma (α + α)) := by
  set f : ℝ → ℝ := fun x => (x * (1 - x)) ^ (α - 1) with hfdef
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbeta := beta_real α hα0
  have hG2 : 0 < Real.Gamma (α + α) := Real.Gamma_pos_of_pos (by linarith)
  have hBpos : 0 < Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) := by
    have := Real.Gamma_pos_of_pos hα0; positivity
  have hII : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [hfdef, hbeta]; exact hBpos.ne'
  have hint : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hII
    exact hII.mono_set Set.Ioo_subset_Ioc_self
  have hnn : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ f x := fun x h0 h1 =>
    Real.rpow_nonneg (mul_nonneg h0 (by linarith)) _
  have hA := lemma_A_1 f (fun x hx => hnn x hx.1.le hx.2.le)
    (by
      intro x hx y hy hxy
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hy0, hy1⟩ := hy
      apply Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith))
    (by intro x _; simp only [hfdef]; ring_nf)
    hint
  have hup := (hA.2 K hK).2
  have hev : 0 ≤ (if Even K then (∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 / (K : ℝ)), f u) else 0) := by
    split_ifs with he
    · have hK2 : 2 ≤ K := by obtain ⟨r, hr⟩ := he; omega
      have hK2R : (2 : ℝ) ≤ K := by exact_mod_cast hK2
      have : 1 / (K : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hKR (by norm_num)]; linarith
      have hpos : 0 < 1 / (K : ℝ) := by positivity
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu; exact hnn u (by linarith [hu.1]) (by linarith [hu.2])
    · exact le_rfl
  have hod : 0 ≤ (if Odd K then (∫ u in ((K : ℝ) - 1) / (2 * K)..((K : ℝ) + 1) / (2 * K), f u)
      else 0) := by
    split_ifs with ho
    · have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have ha : 0 ≤ ((K : ℝ) - 1) / (2 * K) := div_nonneg (by linarith) (by positivity)
      have hb : ((K : ℝ) + 1) / (2 * K) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hab : ((K : ℝ) - 1) / (2 * K) ≤ ((K : ℝ) + 1) / (2 * K) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      apply intervalIntegral.integral_nonneg hab
      intro u hu; exact hnn u (by linarith [hu.1]) (by linarith [hu.2])
    · exact le_rfl
  have hR : (1 / (K : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 K, f ((ℓ : ℝ) / K) ≤
      Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) := by
    have : (∫ u in (0 : ℝ)..1, f u) = Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) := hbeta
    linarith
  have hR' : ∑ ℓ ∈ Finset.Ico 1 K, f ((ℓ : ℝ) / K) ≤
      K * (Real.Gamma α * Real.Gamma α / Real.Gamma (α + α)) := by
    have := mul_le_mul_of_nonneg_left hR hKR.le
    rwa [← mul_assoc, mul_one_div_cancel hKR.ne', one_mul] at this
  have hterm : ∀ ℓ ∈ Finset.Ico 1 K, (ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1) =
      (K : ℝ) ^ (α - 1) * (K : ℝ) ^ (α - 1) * f ((ℓ : ℝ) / K) := by
    intro ℓ hℓ
    rw [Finset.mem_Ico] at hℓ
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.1
    have hℓK : (ℓ : ℝ) < K := by exact_mod_cast hℓ.2
    simp only [hfdef]
    have e1 : (ℓ : ℝ) / K * (1 - (ℓ : ℝ) / K) = (ℓ * (K - ℓ)) / (K * K) := by field_simp
    rw [e1, Real.div_rpow (by nlinarith) (by positivity), Real.mul_rpow hℓ0.le (by linarith),
      Real.mul_rpow hKR.le hKR.le]
    have : 0 < (K : ℝ) ^ (α - 1) := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  calc (K : ℝ) ^ (α - 1) * (K : ℝ) ^ (α - 1) * ∑ ℓ ∈ Finset.Ico 1 K, f ((ℓ : ℝ) / K)
      ≤ (K : ℝ) ^ (α - 1) * (K : ℝ) ^ (α - 1) *
          (K * (Real.Gamma α * Real.Gamma α / Real.Gamma (α + α))) :=
        mul_le_mul_of_nonneg_left hR' (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem bound (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖)) /
        ((2 : ℝ) ^ (1 - max (1 - 2 * α) 0) * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k := by
  intro ρ C
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hG1 : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma (2 * α) := Real.Gamma_pos_of_pos (by linarith)
  have hGa : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα0.ne'
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hN : 0 < ‖nu‖ := norm_pos_iff.mpr hnu
  set m := ‖mu‖ with hm
  set L := ‖lam‖ with hLdef
  set N := ‖nu‖ with hNdef
  set q := max (1 - 2 * α) 0 with hq
  set B : ℝ := Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) with hB
  have hBpos : 0 < B := by rw [hB]; have := Real.Gamma_pos_of_pos (show 0 < α + α by linarith); positivity
  set E : ℝ := (2 : ℝ) ^ (2 - q) * (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * L * N with hE
  have hEpos : 0 < E := by positivity
  set S := Real.sqrt (m ^ 2 + E) with hS
  have hS2 : S ^ 2 = m ^ 2 + E := Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ m := norm_nonneg _
  set D : ℝ := (2 : ℝ) ^ (1 - q) * α ^ α / 2 with hD
  have hDpos : 0 < D := by positivity
  have hρdef : ρ = (m + S) / (2 * D) := by
    show (m + S) / ((2 : ℝ) ^ (1 - q) * α ^ α) = _
    rw [hD]; ring
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hCdef : C = N / (Real.Gamma (α + 1) * ρ) := rfl
  have hC : 0 < C := by rw [hCdef]; positivity
  set P : ℝ := (2 : ℝ) ^ q with hP
  have hPD : P * D = α ^ α := by
    rw [hP, hD, ← mul_div_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
      show q + (1 - q) = 1 by ring, Real.rpow_one]; ring
  have hquad : L * C * B + m = D * ρ := by
    have h1 : D * ρ ^ 2 - m * ρ = E / (4 * D) := by
      rw [hρdef]; field_simp; nlinarith [hS2]
    have h2 : E / (4 * D) = L * N * B / Real.Gamma (α + 1) := by
      rw [hE, hD, hB, hGa, show α + α = 2 * α by ring]
      have h22 : (2 : ℝ) ^ (2 - q) = 2 * (2 : ℝ) ^ (1 - q) := by
        rw [show 2 - q = (1 - q) + 1 by ring, Real.rpow_add_one (by norm_num)]; ring
      have haa : α ^ (α - 1) = α ^ α / α := by rw [Real.rpow_sub_one hα0.ne']
      rw [h22, haa]
      have : 0 < (2 : ℝ) ^ (1 - q) := by positivity
      have : 0 < α ^ α := by positivity
      field_simp
      norm_num
    have h3 : L * C * B * ρ = L * N * B / Real.Gamma (α + 1) := by
      rw [hCdef]; field_simp
    have h4 : (L * C * B + m) * ρ = D * ρ * ρ := by nlinarith [h1, h2, h3]
    exact mul_right_cancel₀ hρ.ne' h4
  -- the elementary power inequality (k/(k+1))^{2α-1} ≤ 2^{(1-2α)_+}
  have hpow : ∀ K : ℝ, 1 ≤ K → K ^ (2 * α - 1) ≤ P * (K + 1) ^ (2 * α - 1) := by
    intro K hK
    have hK0 : 0 < K := by linarith
    rcases le_or_gt 0 (2 * α - 1) with h | h
    · have hq0 : q = 0 := by rw [hq]; exact max_eq_right (by linarith)
      rw [hP, hq0, Real.rpow_zero, one_mul]
      exact Real.rpow_le_rpow hK0.le (by linarith) h
    · have hq1 : q = 1 - 2 * α := by rw [hq]; exact max_eq_left (by linarith)
      have e : K ^ (2 * α - 1) = (2 : ℝ) ^ q * (2 * K) ^ (2 * α - 1) := by
        rw [Real.mul_rpow (by norm_num) hK0.le, ← mul_assoc, ← Real.rpow_add (by norm_num), hq1,
          show 1 - 2 * α + (2 * α - 1) = 0 by ring, Real.rpow_zero, one_mul]
      rw [e, hP]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) h.le
  clear_value P D S E C ρ B q m L N
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, hk => omega
    | 1, _, _ =>
      simp only [coeff, Nat.cast_one, Real.one_rpow, mul_one, pow_one]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hG1.le, hCdef]
      apply le_of_eq
      field_simp
      exact hNdef.symm
    | j + 2, ih, _ =>
      obtain ⟨K, hKdef⟩ : ∃ K, K = j + 1 := ⟨_, rfl⟩
      rw [coeff_rec, ← hKdef]
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by rw [hKdef]; push_cast; linarith
      have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
      set A : ℝ := (K : ℝ) ^ (α - 1) with hA
      set A1 : ℝ := ((K : ℝ) + 1) ^ (α - 1) with hA1
      set g : ℝ := Real.Gamma (α * (K : ℝ) + 1) / Real.Gamma (α * (K : ℝ) + α + 1) with hg
      have hg0 : 0 ≤ g := div_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
        (Real.Gamma_pos_of_pos (by positivity)).le
      have hgle : g ≤ ((K : ℝ) + 1) ^ (-α) / α ^ α := by
        refine (gamma_ratio α K hα0 hα1 hK0.le).trans (le_of_eq ?_)
        rw [Real.mul_rpow hα0.le (by linarith), Real.rpow_neg hα0.le]; ring
      -- T1 and T2
      have hT1 : A * A * K * ((K : ℝ) + 1) ^ (-α) ≤ P * A1 := by
        have e1 : A * A * K = (K : ℝ) ^ (2 * α - 1) := by
          rw [hA, ← Real.rpow_add hK0, ← Real.rpow_add_one hK0.ne']; congr 1; ring
        have e2 : A1 = ((K : ℝ) + 1) ^ (2 * α - 1) * ((K : ℝ) + 1) ^ (-α) := by
          rw [hA1, ← Real.rpow_add (by linarith)]; congr 1; ring
        rw [e1, e2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hpow K hK1) (by positivity)
      have hT2 : A * ((K : ℝ) + 1) ^ (-α) ≤ P * A1 := by
        refine le_trans ?_ hT1
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : 1 ≤ A * K := by
          rw [hA, ← Real.rpow_add_one hK0.ne']
          exact Real.one_le_rpow hK1 (by linarith)
        have hA0 : 0 < A := by positivity
        calc A = A * 1 := (mul_one A).symm
          _ ≤ A * (A * K) := mul_le_mul_of_nonneg_left this hA0.le
          _ = A * A * K := by ring
      have hApos : 0 < A := by positivity
      have hA1pos : 0 < A1 := by positivity
      clear_value A A1 g
      have hconv : ‖∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ)‖ ≤
          C ^ 2 * ρ ^ K * (A * A * K * B) := by
        refine (norm_sum_le _ _).trans ?_
        have hks := kernel_sum α hα0 hα1 K (by omega)
        rw [← hA, ← hB] at hks
        calc ∑ ℓ ∈ Finset.Ico 1 K, ‖coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ)‖
            ≤ ∑ ℓ ∈ Finset.Ico 1 K, C ^ 2 * ρ ^ K * ((ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1)) := by
              apply Finset.sum_le_sum
              intro ℓ hℓ
              rw [Finset.mem_Ico] at hℓ
              rw [norm_mul]
              have b1 := ih ℓ (by omega) (by omega)
              have b2 := ih (K - ℓ) (by omega) (by omega)
              have hcast : ((K - ℓ : ℕ) : ℝ) = (K : ℝ) - ℓ := by rw [Nat.cast_sub (by omega)]
              rw [hcast] at b2
              have hρK : ρ ^ ℓ * ρ ^ (K - ℓ) = ρ ^ K := by rw [← pow_add]; congr 1; omega
              have hl0 : (0 : ℝ) ≤ ((K : ℝ) - ℓ) := by
                have : (ℓ : ℝ) ≤ K := by exact_mod_cast hℓ.2.le
                linarith
              calc ‖coeff α lam mu nu ℓ‖ * ‖coeff α lam mu nu (K - ℓ)‖
                  ≤ (C * (ℓ : ℝ) ^ (α - 1) * ρ ^ ℓ) * (C * ((K : ℝ) - ℓ) ^ (α - 1) * ρ ^ (K - ℓ)) :=
                    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
                _ = C ^ 2 * (ρ ^ ℓ * ρ ^ (K - ℓ)) * ((ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1)) := by
                    ring
                _ = C ^ 2 * ρ ^ K * ((ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1)) := by rw [hρK]
          _ = C ^ 2 * ρ ^ K * ∑ ℓ ∈ Finset.Ico 1 K, ((ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1)) := by
              rw [Finset.mul_sum]
          _ ≤ C ^ 2 * ρ ^ K * (A * A * K * B) := mul_le_mul_of_nonneg_left hks (by positivity)
      have hprev := ih K (by omega) (by omega)
      rw [← hA] at hprev
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0]
      have hcK : ((j + 2 : ℕ) : ℝ) = (K : ℝ) + 1 := by rw [hKdef]; push_cast; ring
      rw [hcK, show j + 2 = K + 1 by omega, ← hA1]
      have hX : ‖lam * ∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ) +
          mu * coeff α lam mu nu K‖ ≤
          L * (C ^ 2 * ρ ^ K * (A * A * K * B)) + m * (C * A * ρ ^ K) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, ← hLdef, ← hm]
        exact add_le_add (mul_le_mul_of_nonneg_left hconv hL.le)
          (mul_le_mul_of_nonneg_left hprev hm0)
      have hKa : 0 ≤ ((K : ℝ) + 1) ^ (-α) := by positivity
      have hαα : 0 < α ^ α := by positivity
      calc ‖lam * ∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ) +
            mu * coeff α lam mu nu K‖ * g
          ≤ (L * (C ^ 2 * ρ ^ K * (A * A * K * B)) + m * (C * A * ρ ^ K)) *
              (((K : ℝ) + 1) ^ (-α) / α ^ α) := mul_le_mul hX hgle hg0 (by have := hBpos.le; positivity)
        _ = C * ρ ^ K / α ^ α * (L * C * B * (A * A * K * ((K : ℝ) + 1) ^ (-α)) +
              m * (A * ((K : ℝ) + 1) ^ (-α))) := by ring
        _ ≤ C * ρ ^ K / α ^ α * (L * C * B * (P * A1) + m * (P * A1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact add_le_add (mul_le_mul_of_nonneg_left hT1 (by positivity))
                (mul_le_mul_of_nonneg_left hT2 hm0)
        _ = C * ρ ^ K / α ^ α * (P * A1 * (L * C * B + m)) := by ring
        _ = C * A1 * ρ ^ (K + 1) := by
              rw [hquad, pow_succ]
              have : P * A1 * (D * ρ) = (P * D) * A1 * ρ := by ring
              rw [this, hPD]
              field_simp

end Aux_FRR_B49

open FracRiccati.Radius in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖)) /
        ((2 : ℝ) ^ (1 - max (1 - 2 * α) 0) * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k :=
  Aux_FRR_B49.bound α hα0 hα1 lam mu nu hlam hnu
