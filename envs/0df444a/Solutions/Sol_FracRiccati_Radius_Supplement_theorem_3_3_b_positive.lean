-- Prove2me | solution 1 for FracRiccati.Radius.Supplement.theorem_3_3_b_positive
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:34.764077+00:00
-- url     : https://prove2.me/submissions/e965c034-170f-4353-b25f-e815a557e88a

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

open FracRiccati
open FracRiccati.Radius
open FracRiccati.Radius.Supplement

open Filter Topology

theorem solution (α l m n : ℝ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hl : 0 < l) (hm : 0 ≤ m) (hn : 0 < n) :
    let R := radius α (coeff α l m n)
    0 < R ∧ R < ⊤ ∧
    StrictMonoOn (psiReal α l m n) (Set.Ico 0 R.toReal) ∧
    Tendsto (psiReal α l m n) (nhdsWithin R.toReal (Set.Ico 0 R.toReal)) atTop ∧
    (¬ ∃ f : ℝ → ℝ,
      ContinuousAt f R.toReal ∧ Set.EqOn f (psiReal α l m n) (Set.Ico 0 R.toReal)) := by
        intro R
        simp only [R]
        clear R
        let a : ℕ → ℝ := fun k => (coeff α l m n k).re
        let c : ℕ → ℝ := fun k => Real.Gamma (α * (k:ℝ) + 1) / Real.Gamma (α * (k:ℝ) + α + 1)
        have hreal : ∀ k, coeff α l m n k = (a k : ℂ) := by
          intro k
          induction k using Nat.strong_induction_on with
          | _ k ih =>
            match k with
            | 0 => simp [a, coeff.eq_1]
            | 1 =>
              simp only [a, coeff.eq_2]
              rw [← Complex.ofReal_div, Complex.ofReal_re]
            | j+2 =>
              have e : coeff α l m n (j+2) = (((l * ∑ ℓ ∈ (Finset.Ico 1 (j + 1)).attach, a ℓ.1 * a (j + 1 - ℓ.1) +
                  m * a (j + 1)) * c (j+1) : ℝ) : ℂ) := by
                rw [coeff.eq_3]
                have h1 : ∀ ℓ ∈ (Finset.Ico 1 (j + 1)).attach, coeff α l m n ℓ.1 * coeff α l m n (j + 1 - ℓ.1)
                    = ((a ℓ.1 * a (j + 1 - ℓ.1) : ℝ) : ℂ) := by
                  intro ℓ _
                  have := (Finset.mem_Ico.mp ℓ.2).2
                  rw [ih ℓ.1 (by omega), ih (j + 1 - ℓ.1) (by omega)]
                  push_cast; ring
                rw [Finset.sum_congr rfl h1, ih (j+1) (by omega)]
                simp only [c]
                push_cast
                ring
              simp only [a]
              rw [e, Complex.ofReal_re]
        have a0 : a 0 = 0 := by simp [a, coeff.eq_1]
        have a1 : a 1 = n / Real.Gamma (α + 1) := by
          simp only [a, coeff.eq_2]
          rw [← Complex.ofReal_div, Complex.ofReal_re]
        have hrec : ∀ j, a (j+2) = (l * ∑ ℓ ∈ Finset.Ico 1 (j + 1), a ℓ * a (j + 1 - ℓ) +
                  m * a (j + 1)) * c (j+1) := by
          intro j
          have h := coeff.eq_3 α l m n j
          simp only [hreal] at h
          have h2 := congrArg Complex.re h
          rw [Complex.ofReal_re] at h2
          rw [h2, ← Finset.sum_attach (Finset.Ico 1 (j + 1)) (fun ℓ => a ℓ * a (j + 1 - ℓ))]
          simp only [c]
          norm_cast
        have hc_pos : ∀ k, 0 < c k := by
          intro k
          simp only [c]
          apply div_pos <;> apply Real.Gamma_pos_of_pos <;> positivity
        clear_value a
        have ha_nn : ∀ k, 0 ≤ a k := by
          intro k
          induction k using Nat.strong_induction_on with
          | _ k ih =>
            match k with
            | 0 => simp [a0]
            | 1 => rw [a1]; exact div_nonneg hn.le (Real.Gamma_pos_of_pos (by linarith)).le
            | j+2 =>
              rw [hrec]
              apply mul_nonneg _ (hc_pos _).le
              apply add_nonneg
              · apply mul_nonneg hl.le
                apply Finset.sum_nonneg
                intro ℓ hℓ
                have := (Finset.mem_Ico.mp hℓ).2
                exact mul_nonneg (ih _ (by omega)) (ih _ (by omega))
              · exact mul_nonneg hm (ih _ (by omega))
        have a1_pos : 0 < a 1 := by
          rw [a1]; exact div_pos hn (Real.Gamma_pos_of_pos (by linarith))
        have hcx : ∀ k : ℕ, c k = Real.Gamma (α * k + 1) / Real.Gamma ((α * k + 1) + α) := by
          intro k; simp only [c]; ring_nf
        clear_value c
        have hG_low : ∀ x : ℝ, 1 ≤ x → 1 / (x * (x + 1)) ≤ Real.Gamma x / Real.Gamma (x + α) := by
          intro x hx1
          have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
          have h2 : Real.Gamma (x + 2) = (x+1) * x * Real.Gamma x := by
            rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith), Real.Gamma_add_one (by linarith)]
            ring
          have hconv := Real.convexOn_Gamma.2 (show x ∈ Set.Ioi 0 by simp; linarith)
            (show x + 2 ∈ Set.Ioi 0 by simp; linarith) (show 0 ≤ 1 - α/2 by linarith)
            (show 0 ≤ α/2 by linarith) (by ring)
          simp only [smul_eq_mul] at hconv
          rw [show (1 - α/2) * x + α/2 * (x+2) = x + α by ring, h2] at hconv
          have hb : Real.Gamma (x + α) ≤ x * (x+1) * Real.Gamma x := by
            have h11 := mul_le_mul hx1 (show 1 ≤ x+1 by linarith only [hx1]) zero_le_one (by linarith only [hx1])
            have : 0 ≤ x * (x+1) - 1 := by linarith only [h11]
            have := mul_nonneg (mul_nonneg (show 0 ≤ 1 - α/2 by linarith only [hα2]) this) hG.le
            linarith only [hconv, this]
          have hGa : 0 < Real.Gamma (x + α) := Real.Gamma_pos_of_pos (by linarith only [hx1, hα])
          have hx0 : 0 < x := by linarith only [hx1]
          rw [div_le_div_iff₀ (mul_pos hx0 (by linarith only [hx1])) hGa]
          linarith only [hb]
        have hc_low : ∀ k : ℕ, 1 / ((α * k + 1) * (α * k + 2)) ≤ c k := by
          intro k
          rw [hcx, show α * (k:ℝ) + 2 = (α * k + 1) + 1 by ring]
          apply hG_low
          have : 0 ≤ α * k := by positivity
          linarith
        have hc_up : ∀ δ > 0, ∀ᶠ k : ℕ in atTop, c k ≤ δ := by
          intro δ hδ
          rcases le_or_gt 1 α with h1 | h1
          · have hG_up : ∀ x : ℝ, 2 ≤ x → Real.Gamma x / Real.Gamma (x + α) ≤ 1 / x := by
              intro x hx2
              have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
              have hmono : Real.Gamma (x + 1) ≤ Real.Gamma (x + α) :=
                Real.Gamma_strictMonoOn_Ici.monotoneOn (show x + 1 ∈ Set.Ici 2 by simp; linarith)
                  (show x + α ∈ Set.Ici 2 by simp; linarith) (by linarith)
              rw [Real.Gamma_add_one (by linarith)] at hmono
              rw [div_le_div_iff₀ (by linarith [mul_pos (show (0:ℝ) < x by linarith) hG]) (by linarith)]
              linarith
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (α * δ))
            filter_upwards [eventually_ge_atTop (max N 1)] with k hk
            have hk1 : (1:ℝ) ≤ k := by exact_mod_cast le_of_max_le_right hk
            have hkN : (N:ℝ) ≤ k := by exact_mod_cast le_of_max_le_left hk
            have hαk : 1 ≤ α * k := one_le_mul_of_one_le_of_one_le h1 hk1
            rw [hcx]
            refine (hG_up _ (by linarith only [hαk])).trans ?_
            have hαδ : 0 < α * δ := mul_pos hα hδ
            have hN' := (div_lt_iff₀ hαδ).1 hN
            have hm' := mul_le_mul_of_nonneg_left hkN hαδ.le
            rw [div_le_iff₀ (by linarith only [hαk])]
            linarith only [hN', hm', hδ]
          · have hG_up : ∀ x : ℝ, 1 ≤ x → Real.Gamma x / Real.Gamma (x + α) ≤ 2 * x ^ (-α) := by
              intro x hx1
              have hGa : 0 < Real.Gamma (x + α) := Real.Gamma_pos_of_pos (by linarith)
              have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
              have hlc := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (show 0 < x + α by linarith)
                (show 0 < x + α + 1 by linarith) hα (show 0 < 1 - α by linarith) (by ring)
              rw [show α * (x + α) + (1 - α) * (x + α + 1) = x + 1 by ring, Real.Gamma_add_one (by linarith),
                Real.Gamma_add_one (by linarith), Real.mul_rpow (by linarith) hGa.le] at hlc
              have e : Real.Gamma (x + α) ^ α * ((x + α) ^ (1 - α) * Real.Gamma (x + α) ^ (1 - α))
                  = (x + α) ^ (1 - α) * Real.Gamma (x + α) := by
                rw [mul_left_comm, ← Real.rpow_add hGa, show α + (1 - α) = 1 by ring, Real.rpow_one]
              rw [e] at hlc
              have hp : (x + α) ^ (1 - α) ≤ 2 * x ^ (1 - α) := by
                calc (x + α) ^ (1 - α) ≤ (2 * x) ^ (1 - α) :=
                      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
                  _ = 2 ^ (1 - α) * x ^ (1 - α) := Real.mul_rpow (by norm_num) (by linarith)
                  _ ≤ 2 * x ^ (1 - α) := by
                      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (zero_le_one.trans hx1) _)
                      calc (2:ℝ) ^ (1 - α) ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hα])
                        _ = 2 := Real.rpow_one 2
              have hxe : x ^ (1 - α) = x * x ^ (-α) := by
                rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
              rw [div_le_iff₀ hGa]
              have : x * Real.Gamma x ≤ x * (2 * x ^ (-α) * Real.Gamma (x + α)) := by
                rw [hxe] at hp
                have := mul_le_mul_of_nonneg_right hp hGa.le
                linarith only [hlc, this]
              exact le_of_mul_le_mul_left this (by linarith only [hx1])
            have ht : Tendsto (fun k : ℕ => (α * (k:ℝ) + 1) ^ (-α)) atTop (nhds 0) := by
              apply (tendsto_rpow_neg_atTop hα).comp
              apply tendsto_atTop_add_const_right
              exact Tendsto.const_mul_atTop hα tendsto_natCast_atTop_atTop
            filter_upwards [(tendsto_order.1 ht).2 (δ/2) (by positivity)] with k hk
            rw [hcx]
            refine (hG_up _ ?_).trans ?_
            · have : 0 ≤ α * k := by positivity
              linarith
            · linarith
        have hconv : ∀ b : ℕ → ℝ, (∀ i, 0 ≤ b i) → ∀ N, ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ)
            ≤ (∑ k ∈ Finset.range N, b k) ^ 2 := by
          intro b hb N
          have hE : ∀ N, ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range (j+1), b ℓ * b (j - ℓ)
              = ∑ ℓ ∈ Finset.range N, b ℓ * ∑ k ∈ Finset.range (N - ℓ), b k := by
            intro N
            induction N with
            | zero => simp
            | succ N ih =>
              rw [Finset.sum_range_succ, ih]
              have h1 : ∀ ℓ ∈ Finset.range (N+1), b ℓ * ∑ k ∈ Finset.range (N + 1 - ℓ), b k
                  = b ℓ * ∑ k ∈ Finset.range (N - ℓ), b k + b ℓ * b (N - ℓ) := by
                intro ℓ hℓ
                have := Finset.mem_range.mp hℓ
                rw [show N + 1 - ℓ = (N - ℓ) + 1 by omega, Finset.sum_range_succ]
                ring
              rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_range_succ (fun ℓ => b ℓ * ∑ k ∈ Finset.range (N - ℓ), b k)]
              simp
          have hS : ∀ M, 0 ≤ ∑ k ∈ Finset.range M, b k := fun M => Finset.sum_nonneg (fun i _ => hb i)
          calc ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ)
              ≤ ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range (j+1), b ℓ * b (j - ℓ) := by
                apply Finset.sum_le_sum
                intro j _
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro ℓ hℓ; simp only [Finset.mem_Ico] at hℓ; simp only [Finset.mem_range]; omega
                · intro i _ _; exact mul_nonneg (hb _) (hb _)
            _ = ∑ ℓ ∈ Finset.range N, b ℓ * ∑ k ∈ Finset.range (N - ℓ), b k := hE N
            _ ≤ ∑ ℓ ∈ Finset.range N, b ℓ * ∑ k ∈ Finset.range N, b k := by
                apply Finset.sum_le_sum
                intro ℓ _
                apply mul_le_mul_of_nonneg_left _ (hb ℓ)
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
                · intro i _ _; exact hb i
            _ = (∑ k ∈ Finset.range N, b k) ^ 2 := by rw [← Finset.sum_mul]; ring
        have hboot : ∀ x : ℝ, 0 ≤ x → ∀ K : ℕ, 1 ≤ K → ∀ ε : ℝ, 0 ≤ ε → (∀ j, K ≤ j → x * c j ≤ ε) →
            ε * (4 * l * (∑ k ∈ Finset.range (K+1), a k * x ^ k) + 2 * m) ≤ 1 →
            ∀ N, ∑ k ∈ Finset.range N, a k * x ^ k ≤ 2 * ∑ k ∈ Finset.range (K+1), a k * x ^ k := by
          intro x hx K hK ε hε hc hεA
          set b : ℕ → ℝ := fun k => a k * x ^ k with hb_def
          have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg (ha_nn i) (pow_nonneg hx i)
          set A := ∑ k ∈ Finset.range (K+1), b k with hA
          set S : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, b k with hS_def
          have hSnn : ∀ N, 0 ≤ S N := fun N => Finset.sum_nonneg (fun i _ => hb i)
          have hSmono : ∀ M N, M ≤ N → S M ≤ S N := by
            intro M N hMN
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hMN)
            intro i _ _; exact hb i
          have hstep : ∀ j, K ≤ j → b (j+1) ≤ ε * (l * ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ) + m * b j) := by
            intro j hj
            obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
            have e : b (i + 1 + 1) = x * c (i+1) * (l * ∑ ℓ ∈ Finset.Ico 1 (i+1), b ℓ * b (i + 1 - ℓ) + m * b (i+1)) := by
              simp only [b]
              have : ∀ ℓ ∈ Finset.Ico 1 (i+1), a ℓ * x ^ ℓ * (a (i + 1 - ℓ) * x ^ (i + 1 - ℓ))
                  = x ^ (i+1) * (a ℓ * a (i + 1 - ℓ)) := by
                intro ℓ hℓ
                have := (Finset.mem_Ico.mp hℓ).2
                rw [show x ^ (i+1) = x ^ ℓ * x ^ (i + 1 - ℓ) by rw [← pow_add]; congr 1; omega]
                ring
              rw [hrec i, Finset.sum_congr rfl this, ← Finset.mul_sum]
              ring
            rw [e]
            apply mul_le_mul_of_nonneg_right (hc _ hj)
            apply add_nonneg
            · apply mul_nonneg hl.le
              apply Finset.sum_nonneg; intro i _; exact mul_nonneg (hb _) (hb _)
            · exact mul_nonneg hm (hb _)
          have hsplit : ∀ N, K ≤ N → S (N+1) = A + ∑ j ∈ Finset.Ico K N, b (j+1) := by
            intro N hN
            induction N, hN using Nat.le_induction with
            | base => simp [S, A]
            | succ N hKN ih =>
              rw [Finset.sum_Ico_succ_top hKN, ← add_assoc, ← ih]
              simp only [S]
              rw [Finset.sum_range_succ _ (N+1)]
          have hmain : ∀ N, K + 1 ≤ N → S N ≤ 2 * A := by
            intro N hN
            induction N, hN using Nat.le_induction with
            | base => have := hSnn (K+1); simp only [S, A] at this ⊢; linarith
            | succ N hKN ih =>
              rw [hsplit N (by omega)]
              have h1 : ∑ j ∈ Finset.Ico K N, b (j+1) ≤ ε * (l * S N ^ 2 + m * S N) := by
                calc ∑ j ∈ Finset.Ico K N, b (j+1)
                    ≤ ∑ j ∈ Finset.Ico K N, ε * (l * ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ) + m * b j) := by
                      apply Finset.sum_le_sum
                      intro j hj
                      exact hstep j (Finset.mem_Ico.mp hj).1
                  _ ≤ ∑ j ∈ Finset.range N, ε * (l * ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ) + m * b j) := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro j hj; simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
                      · intro j _ _
                        apply mul_nonneg hε
                        apply add_nonneg
                        · apply mul_nonneg hl.le
                          apply Finset.sum_nonneg; intro i _; exact mul_nonneg (hb _) (hb _)
                        · exact mul_nonneg hm (hb _)
                  _ = ε * (l * ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.Ico 1 j, b ℓ * b (j - ℓ) + m * S N) := by
                      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  _ ≤ ε * (l * S N ^ 2 + m * S N) := by
                      gcongr
                      exact hconv b hb N
              have hA0 : 0 ≤ A := hSnn (K+1)
              have hSN := hSnn N
              have h2 : l * S N ^ 2 + m * S N ≤ A * (4 * l * A + 2 * m) := by
                have hsq : S N * S N ≤ (2 * A) * (2 * A) := mul_le_mul ih ih hSN (mul_nonneg zero_le_two hA0)
                have e1 := mul_le_mul_of_nonneg_left hsq hl.le
                have e2 := mul_le_mul_of_nonneg_left ih hm
                linarith only [e1, e2]
              have h3 : ε * (l * S N ^ 2 + m * S N) ≤ A := by
                calc ε * (l * S N ^ 2 + m * S N) ≤ ε * (A * (4 * l * A + 2 * m)) :=
                      mul_le_mul_of_nonneg_left h2 hε
                  _ = A * (ε * (4 * l * A + 2 * m)) := by ring
                  _ ≤ A * 1 := mul_le_mul_of_nonneg_left hεA hA0
                  _ = A := mul_one A
              linarith only [h1, h3]
          intro N
          rcases le_or_gt (K+1) N with h | h
          · exact hmain N h
          · have := hSmono N (K+1) h.le
            have hA0 : 0 ≤ A := hSnn (K+1)
            show S N ≤ 2 * A
            have : S (K+1) = A := rfl
            linarith
        set e : ℕ → ENNReal := fun k => ((‖coeff α l m n k‖₊ : ENNReal) ^ (-(1 / (α * (k:ℝ))) : ℝ)) with he_def
        have hR : radius α (coeff α l m n) = liminf e atTop := rfl
        have he_pos : ∀ k : ℕ, 0 < a k → e k = ENNReal.ofReal ((a k)⁻¹ ^ (1 / (α * k))) := by
          intro k hk
          simp only [e, hreal]
          rw [show (‖(a k : ℂ)‖₊ : ENNReal) = ENNReal.ofReal (a k) by
            rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk], ENNReal.ofReal_rpow_of_pos hk,
            Real.rpow_neg hk.le, Real.inv_rpow hk.le]
        have he_zero : ∀ k : ℕ, 1 ≤ k → a k = 0 → e k = ⊤ := by
          intro k hk h0
          simp only [e, hreal, h0]
          have : (0:ℝ) < α * k := by have : (1:ℝ) ≤ k := by exact_mod_cast hk
                                     positivity
          simp only [Complex.ofReal_zero, nnnorm_zero, ENNReal.coe_zero]
          exact ENNReal.zero_rpow_of_neg (by simp; positivity)
        have hk_pos : ∀ k : ℕ, 1 ≤ k → (0:ℝ) < α * k := by
          intro k hk; have : (1:ℝ) ≤ k := by exact_mod_cast hk
          positivity
        have hpow_eq : ∀ k : ℕ, 1 ≤ k → ∀ y : ℝ, 0 ≤ y → (y ^ k) ^ (1 / (α * k)) = y ^ (1/α) := by
          intro k hk y hy
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
          congr 1
          have := hk_pos k hk
          have : (k:ℝ) ≠ 0 := by have : (1:ℝ) ≤ k := by exact_mod_cast hk
                                 positivity
          field_simp
        have E1 : ∀ k : ℕ, 1 ≤ k → ∀ y : ℝ, 0 < y → a k * y ^ k ≤ 1 → ENNReal.ofReal (y ^ (1/α)) ≤ e k := by
          intro k hk y hy h
          rcases (ha_nn k).eq_or_lt with h0 | h0
          · rw [he_zero k hk h0.symm]; exact le_top
          · rw [he_pos k h0]
            apply ENNReal.ofReal_le_ofReal
            rw [← hpow_eq k hk y hy.le]
            apply Real.rpow_le_rpow (by positivity) _ (by have := hk_pos k hk; positivity)
            rw [← one_div, le_div_iff₀ (by positivity)]; linarith [mul_comm (a k) (y ^ k)]
        have E2 : ∀ k : ℕ, 1 ≤ k → ∀ y : ℝ, 0 < y → ENNReal.ofReal (y ^ (1/α)) < e k → a k * y ^ k ≤ 1 := by
          intro k hk y hy h
          rcases (ha_nn k).eq_or_lt with h0 | h0
          · rw [← h0]; simp
          · rw [he_pos k h0, ENNReal.ofReal_lt_ofReal_iff (by positivity), ← hpow_eq k hk y hy.le] at h
            have := (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (show 0 < 1 / (α * k) by
              have := hk_pos k hk; positivity)).mp h
            rw [← one_div, lt_div_iff₀ (by positivity)] at this; linarith
        have E3 : ∀ k : ℕ, 1 ≤ k → ∀ θ : ℝ, 0 < θ → θ ^ k ≤ a k → e k ≤ ENNReal.ofReal ((θ⁻¹) ^ (1/α)) := by
          intro k hk θ hθ h
          have h0 : 0 < a k := lt_of_lt_of_le (by positivity) h
          rw [he_pos k h0]
          apply ENNReal.ofReal_le_ofReal
          rw [← hpow_eq k hk θ⁻¹ (by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ (by have := hk_pos k hk; positivity)
          rw [inv_pow]
          exact inv_anti₀ (by positivity) h
        have hchain : ∃ θ : ℝ, 0 < θ ∧ ∀ i : ℕ, θ ^ (2^(i+1) - 1) ≤ a (2^(i+1) - 1) := by
          set D : ℝ := 256 / l + 1 with hD_def
          have hD : 1 ≤ D := by have : 0 < 256 / l := by positivity
                                linarith
          have hlD : 256 ≤ l * D := by
            rw [hD_def, mul_add, mul_div_cancel₀ _ hl.ne']; linarith
          set θ := min (a 1 / D) (1/2) with hθ_def
          have hθ : 0 < θ := lt_min (div_pos a1_pos (by linarith)) (by norm_num)
          have hθ1 : θ ≤ 1/2 := min_le_right _ _
          have hθD : θ * D ≤ a 1 := by
            have := min_le_left (a 1 / D) (1/2); rwa [← hθ_def, le_div_iff₀ (by linarith)] at this
          have hinv : ∀ i : ℕ, θ ^ (2^i) * 4^i * D ≤ a (2^(i+1) - 1) := by
            intro i
            induction i with
            | zero => simpa using hθD
            | succ i ih =>
              have hp1 : 2 ≤ 2^(i+1) := by
                calc 2 = 2^1 := by norm_num
                  _ ≤ 2^(i+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
              set p : ℕ := 2^(i+1) with hp
              have hpp2 : 2^(i+1+1) = 2*p := by rw [hp, pow_succ 2 (i+1)]; ring
              have hidx : 2^(i+1+1) - 1 = (2*p - 3) + 2 := by rw [hpp2]; omega
              rw [hidx, hrec]
              have hidx2 : 2*p - 3 + 1 = 2*(p-1) := by omega
              rw [hidx2]
              have hsum : a (p-1) * a (p-1) ≤ ∑ ℓ ∈ Finset.Ico 1 (2*(p-1)), a ℓ * a (2*(p-1) - ℓ) := by
                have := Finset.single_le_sum (f := fun ℓ => a ℓ * a (2*(p-1) - ℓ))
                  (fun ℓ _ => mul_nonneg (ha_nn _) (ha_nn _)) (show p-1 ∈ Finset.Ico 1 (2*(p-1)) by
                    simp only [Finset.mem_Ico]; omega)
                simpa [show 2*(p-1) - (p-1) = p-1 by omega] using this
              have hcl : 1 / (4:ℝ)^(i+3) ≤ c (2*(p-1)) := by
                refine le_trans ?_ (hc_low _)
                apply one_div_le_one_div_of_le (by positivity)
                have hpR : ((2*(p-1) : ℕ) : ℝ) = 2 * (p:ℝ) - 2 := by
                  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
                have hpp : (p:ℝ) = 2^(i+1) := by simp [hp]
                rw [hpR]
                have h4 : (4:ℝ)^(i+3) = 16 * (p:ℝ)^2 := by
                  rw [hpp, show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]; ring
                rw [h4]
                have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp1
                have h0 : 0 ≤ 2 * (p:ℝ) - 2 := by linarith only [hp2]
                have h1 : α * (2 * (p:ℝ) - 2) ≤ 2 * (2 * (p:ℝ) - 2) := mul_le_mul_of_nonneg_right hα2 h0
                have h2 : 0 ≤ α * (2 * (p:ℝ) - 2) := mul_nonneg hα.le h0
                clear hpR hpp h4
                generalize α * (2 * (p:ℝ) - 2) = w at h1 h2 ⊢
                have hw1 : w + 1 ≤ 4 * (p:ℝ) := by linarith only [h1, hp2]
                have hw2 : w + 2 ≤ 4 * (p:ℝ) := by linarith only [h1, hp2]
                have hw3 : 0 ≤ w + 2 := by linarith only [h2]
                have hw4 : 0 ≤ 4 * (p:ℝ) := by linarith only [hp2]
                calc (w + 1) * (w + 2) ≤ (4 * (p:ℝ)) * (4 * (p:ℝ)) := mul_le_mul hw1 hw2 hw3 hw4
                  _ = 16 * (p:ℝ)^2 := by ring
              have hu : 0 ≤ θ ^ (2^i) * 4^i * D := by positivity
              have hsq : (θ ^ (2^i) * 4^i * D)^2 ≤ a (p-1) * a (p-1) := by
                rw [sq]; exact mul_le_mul ih ih hu (ha_nn _)
              have key : l * (θ ^ (2^i) * 4^i * D)^2 * (1 / (4:ℝ)^(i+3))
                  = θ ^ (2^(i+1)) * 4^(i+1) * D * (l * D / 256) := by
                rw [show θ ^ (2^(i+1)) = (θ ^ (2^i))^2 by rw [← pow_mul, pow_succ]]
                field_simp
                ring
              have hT : 0 ≤ θ ^ (2^(i+1)) * 4^(i+1) * D := by positivity
              calc θ ^ 2 ^ (i + 1) * 4 ^ (i + 1) * D ≤ θ ^ (2^(i+1)) * 4^(i+1) * D * (l * D / 256) := by
                    have : 1 ≤ l * D / 256 := by rw [le_div_iff₀ (by norm_num), one_mul]; exact hlD
                    exact le_mul_of_one_le_right hT this
                _ = l * (θ ^ (2^i) * 4^i * D)^2 * (1 / (4:ℝ)^(i+3)) := key.symm
                _ ≤ l * (a (p-1) * a (p-1)) * c (2*(p-1)) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hsq hl.le) hcl (one_div_nonneg.2 (pow_nonneg (by norm_num) _))
                      (mul_nonneg hl.le (mul_nonneg (ha_nn _) (ha_nn _)))
                _ ≤ l * (∑ ℓ ∈ Finset.Ico 1 (2*(p-1)), a ℓ * a (2*(p-1) - ℓ)) * c (2*(p-1)) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hl.le) (hc_pos _).le
                _ ≤ _ := by
                    apply mul_le_mul_of_nonneg_right _ (hc_pos _).le
                    exact le_add_of_nonneg_right (mul_nonneg hm (ha_nn (2*(p-1))))
          refine ⟨θ, hθ, fun i => ?_⟩
          refine le_trans ?_ (hinv i)
          have h2i : 2^i ≤ 2^(i+1) - 1 := by rw [pow_succ]; have := Nat.one_le_two_pow (n := i); omega
          calc θ ^ (2^(i+1) - 1) ≤ θ ^ (2^i) := pow_le_pow_of_le_one hθ.le (hθ1.trans (by norm_num)) h2i
            _ = θ ^ (2^i) * 1 * 1 := by ring
            _ ≤ θ ^ (2^i) * 4^i * D :=
                mul_le_mul (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (pow_nonneg hθ.le _)) hD
                  zero_le_one (mul_nonneg (pow_nonneg hθ.le _) (pow_nonneg (by norm_num) _))
        have hRtop : radius α (coeff α l m n) < ⊤ := by
          obtain ⟨θ, hθ, hch⟩ := hchain
          rw [hR]
          refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (ENNReal.ofReal_lt_top (r := (θ⁻¹) ^ (1/α)))
          rw [frequently_atTop]
          intro N
          refine ⟨2^(N+1) - 1, ?_, E3 _ ?_ θ hθ (hch N)⟩
          · have := Nat.lt_two_pow_self (n := N+1); omega
          · have := Nat.one_le_two_pow (n := N); rw [pow_succ]; omega
        have hRlow : ∀ x : ℝ, 0 < x → ∀ C : ℝ, (∀ k, a k * x ^ k ≤ C) → ∀ q : ℝ, 0 < q → q < 1 →
            ENNReal.ofReal ((q * x) ^ (1/α)) ≤ radius α (coeff α l m n) := by
          intro x hx C hC q hq hq1
          rw [hR]
          refine le_liminf_of_le (by isBoundedDefault) ?_
          have ht : Tendsto (fun k : ℕ => C * q ^ k) atTop (nhds 0) := by
            simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul C
          filter_upwards [(tendsto_order.1 ht).2 1 one_pos, eventually_ge_atTop 1] with k hk hk1
          apply E1 k hk1 _ (by positivity)
          rw [mul_pow]
          have := hC k
          calc a k * (q ^ k * x ^ k) = (a k * x ^ k) * q ^ k := by ring
            _ ≤ C * q ^ k := mul_le_mul_of_nonneg_right this (by positivity)
            _ ≤ 1 := hk.le
        have hRpos : 0 < radius α (coeff α l m n) := by
          obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hc_up 1 one_pos)
          set K := max K0 1 with hK
          set P := ∑ k ∈ Finset.range (K+1), a k with hP_def
          have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => ha_nn i)
          set x := min 1 (1 / (4*l*P + 2*m + 1)) with hx_def
          have hlP : 0 ≤ 4 * l * P := mul_nonneg (by linarith only [hl]) hP
          have hx0 : 0 < x := lt_min one_pos (one_div_pos.2 (by linarith only [hlP, hm]))
          have hx1 : x ≤ 1 := min_le_left _ _
          have hx2 : x ≤ 1 / (4*l*P + 2*m + 1) := min_le_right _ _
          set A := ∑ k ∈ Finset.range (K+1), a k * x ^ k with hA_def
          have hAP : A ≤ P := Finset.sum_le_sum (fun k _ =>
            mul_le_of_le_one_right (ha_nn k) (pow_le_one₀ hx0.le hx1))
          have hA0 : 0 ≤ A := Finset.sum_nonneg (fun k _ => mul_nonneg (ha_nn k) (pow_nonneg hx0.le k))
          have hlA : 0 ≤ 4 * l * A := mul_nonneg (by linarith only [hl]) hA0
          have hlAP : 4 * l * A ≤ 4 * l * P := mul_le_mul_of_nonneg_left hAP (by linarith only [hl])
          have hcond : x * (4 * l * A + 2 * m) ≤ 1 := by
            calc x * (4 * l * A + 2 * m) ≤ (1 / (4*l*P + 2*m + 1)) * (4 * l * P + 2 * m) := by
                  apply mul_le_mul hx2 (by linarith only [hlAP]) (by linarith only [hlA, hm])
                    (one_div_nonneg.2 (by linarith only [hlP, hm]))
              _ ≤ 1 := by
                  rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith only [hlP, hm])]; linarith only
          have hbd := hboot x hx0.le K (le_max_right _ _) x hx0.le (fun j hj => by
            have := hK0 j (le_trans (le_max_left _ _) hj)
            exact mul_le_of_le_one_right hx0.le this) hcond
          have hk : ∀ k, a k * x ^ k ≤ 2 * A := fun k => le_trans (Finset.single_le_sum
            (f := fun i => a i * x ^ i) (fun i _ => mul_nonneg (ha_nn i) (pow_nonneg hx0.le i))
            (Finset.self_mem_range_succ k)) (hbd (k+1))
          have := hRlow x hx0 _ hk (1/2) (by norm_num) (by norm_num)
          exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (mul_pos (by norm_num) hx0) _)) this
        set r := (radius α (coeff α l m n)).toReal with hr_def
        have hRr : radius α (coeff α l m n) = ENNReal.ofReal r := (ENNReal.ofReal_toReal hRtop.ne).symm
        have hr : 0 < r := ENNReal.toReal_pos hRpos.ne' hRtop.ne
        have hsumm : ∀ x : ℝ, 0 ≤ x → x < r ^ α → Summable (fun k => a k * x ^ k) := by
          intro x hx hxX
          have hX0 : 0 < r ^ α := by positivity
          set y := (x + r ^ α) / 2 with hy_def
          have hy : 0 < y := by rw [hy_def]; linarith
          have hyX : y < r ^ α := by rw [hy_def]; linarith
          have hxy : x < y := by rw [hy_def]; linarith
          have hyr : y ^ (1/α) < r := by
            calc y ^ (1/α) < (r ^ α) ^ (1/α) := Real.rpow_lt_rpow hy.le hyX (by positivity)
              _ = r := by rw [← Real.rpow_mul hr.le, mul_one_div_cancel hα.ne', Real.rpow_one]
          have hlt : ENNReal.ofReal (y ^ (1/α)) < liminf e atTop := by
            rw [← hR, hRr]; exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hyr
          have hev := eventually_lt_of_lt_liminf hlt
          apply Summable.of_norm_bounded_eventually (g := fun k => (x/y)^k)
            (summable_geometric_of_lt_one (by positivity) ((div_lt_one hy).2 hxy))
          rw [Nat.cofinite_eq_atTop]
          filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
          have h1 := E2 k hk1 y hy hk
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha_nn k) (pow_nonneg hx k))]
          calc a k * x ^ k = (a k * y ^ k) * (x/y) ^ k := by
                rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hy.ne']
            _ ≤ 1 * (x/y) ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (x/y) ^ k := one_mul _
        have hpsi : ∀ t : ℝ, 0 ≤ t → psiReal α l m n t = ∑' k, a k * (t ^ α) ^ k := by
          intro t ht
          simp only [psiReal, psi, hreal]
          have : ∀ k : ℕ, (a k : ℂ) * ((t ^ (α * (k:ℝ)) : ℝ) : ℂ) = ((a k * (t ^ α) ^ k : ℝ) : ℂ) := by
            intro k; rw [Real.rpow_mul ht, Real.rpow_natCast]; push_cast; ring
          simp only [this]
          rw [← Complex.ofReal_tsum, Complex.ofReal_re]
        have hdiv : ∀ M : ℝ, ∃ N, M < ∑ k ∈ Finset.range N, a k * (r ^ α) ^ k := by
          by_contra hcon
          push Not at hcon
          obtain ⟨M, hM⟩ := hcon
          set X := r ^ α with hX
          have hX0 : 0 < X := by positivity
          have hM0 : 0 ≤ M := by simpa using hM 0
          set δ := 1 / (2 * X * (8 * l * M + 2 * m) + 1) with hδ
          have hQ : 0 ≤ 2 * X * (8 * l * M + 2 * m) :=
            mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by linarith) hM0) (by linarith))
          have hδ0 : 0 < δ := one_div_pos.2 (by linarith)
          obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hc_up δ hδ0)
          set K := max K0 1 with hK
          have hK1 : 1 ≤ K := le_max_right _ _
          set lam : ℝ := 2 ^ ((K:ℝ)⁻¹) with hlam
          have hlamK : lam ^ K = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
          have hK1R : (1:ℝ) ≤ K := by exact_mod_cast hK1
          have hlam1 : 1 < lam := Real.one_lt_rpow (by norm_num) (by positivity)
          have hlam2 : lam ≤ 2 := by
            calc lam ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (inv_le_one_of_one_le₀ hK1R)
              _ = 2 := Real.rpow_one 2
          set x := lam * X with hx
          have hx0 : 0 < x := by positivity
          set A := ∑ k ∈ Finset.range (K+1), a k * x ^ k with hA
          have hA0 : 0 ≤ A := Finset.sum_nonneg (fun k _ => mul_nonneg (ha_nn k) (by positivity))
          have hAM : A ≤ 2 * M := by
            calc A ≤ ∑ k ∈ Finset.range (K+1), 2 * (a k * X ^ k) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                  rw [hx, mul_pow]
                  have h2 : lam ^ k ≤ 2 := hlamK ▸ pow_le_pow_right₀ hlam1.le hkK
                  have := mul_le_mul_of_nonneg_right h2 (mul_nonneg (ha_nn k) (pow_nonneg hX0.le k))
                  calc a k * (lam ^ k * X ^ k) = lam ^ k * (a k * X ^ k) := by ring
                    _ ≤ _ := this
              _ = 2 * ∑ k ∈ Finset.range (K+1), a k * X ^ k := by rw [Finset.mul_sum]
              _ ≤ 2 * M := by have := hM (K+1); linarith
          have hcond : x * δ * (4 * l * A + 2 * m) ≤ 1 := by
            have h1 : x * δ * (4 * l * A + 2 * m) ≤ 2 * X * δ * (8 * l * M + 2 * m) := by
              have i0 := mul_le_mul_of_nonneg_left hAM (show 0 ≤ 4 * l by linarith)
              have i1 : 4 * l * A + 2 * m ≤ 8 * l * M + 2 * m := by linarith
              have i2 : x ≤ 2 * X := mul_le_mul_of_nonneg_right hlam2 hX0.le
              have i3 : 0 ≤ 4 * l * A := mul_nonneg (by linarith) hA0
              exact mul_le_mul (mul_le_mul_of_nonneg_right i2 hδ0.le) i1 (by linarith)
                (mul_nonneg (by linarith) hδ0.le)
            have h2 : 2 * X * δ * (8 * l * M + 2 * m) ≤ 1 := by
              have h0 := hQ
              rw [hδ]
              generalize 8 * l * M + 2 * m = Q at h0 ⊢
              rw [show 2 * X * (1 / (2 * X * Q + 1)) * Q = (2 * X * Q) / (2 * X * Q + 1) by ring]
              rw [div_le_one (by linarith)]; linarith
            exact h1.trans h2
          have hbd := hboot x hx0.le K hK1 (x * δ) (mul_nonneg hx0.le hδ0.le)
            (fun j hj => mul_le_mul_of_nonneg_left (hK0 j (le_trans (le_max_left _ _) hj)) hx0.le) hcond
          have hk : ∀ k, a k * x ^ k ≤ 2 * A := fun k => le_trans (Finset.single_le_sum
            (f := fun i => a i * x ^ i) (fun i _ => mul_nonneg (ha_nn i) (pow_nonneg hx0.le i))
            (Finset.self_mem_range_succ k)) (hbd (k+1))
          set q := (lam + 1) / (2 * lam) with hq
          have hq0 : 0 < q := by positivity
          have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
          have hle := hRlow x hx0 _ hk q hq0 hq1
          rw [hRr, ENNReal.ofReal_le_ofReal_iff hr.le] at hle
          have hqx : X < q * x := by
            have e : q * x = (lam + 1) / 2 * X := by rw [hq, hx]; field_simp
            rw [e]
            have := mul_lt_mul_of_pos_right (show 1 < (lam + 1) / 2 by linarith) hX0
            linarith
          have : r < (q * x) ^ (1/α) := by
            calc r = X ^ (1/α) := by rw [hX, ← Real.rpow_mul hr.le, mul_one_div_cancel hα.ne', Real.rpow_one]
              _ < (q * x) ^ (1/α) := Real.rpow_lt_rpow hX0.le hqx (by positivity)
          linarith
        have hT : Tendsto (psiReal α l m n) (nhdsWithin r (Set.Ico 0 r)) atTop := by
          rw [tendsto_atTop]
          intro M
          obtain ⟨N, hN⟩ := hdiv M
          have hc1 : ContinuousAt (fun t : ℝ => t ^ α) r := Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')
          have hcont : ContinuousAt (fun t : ℝ => ∑ k ∈ Finset.range N, a k * (t ^ α) ^ k) r :=
            ContinuousAt.comp (f := fun t : ℝ => t ^ α) (g := fun x : ℝ => ∑ k ∈ Finset.range N, a k * x ^ k)
              (continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_pow k))).continuousAt hc1
          have hev : ∀ᶠ t in nhdsWithin r (Set.Ico 0 r), M < ∑ k ∈ Finset.range N, a k * (t ^ α) ^ k :=
            (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hN)
          filter_upwards [hev, self_mem_nhdsWithin] with t ht htI
          rw [hpsi t htI.1]
          have hsum := hsumm _ (by have := htI.1; positivity) (Real.rpow_lt_rpow htI.1 htI.2 hα)
          refine le_trans ht.le (hsum.sum_le_tsum _ (fun k _ => mul_nonneg (ha_nn k) (by have := htI.1; positivity)))
        refine ⟨hRpos, hRtop, ?_, hT, ?_⟩
        · intro s hs t ht hst
          have hs0 : 0 ≤ s := hs.1
          have ht0 : 0 ≤ t := ht.1
          rw [hpsi s hs0, hpsi t ht0]
          have hsX : s ^ α < r ^ α := Real.rpow_lt_rpow hs0 hs.2 hα
          have htX : t ^ α < r ^ α := Real.rpow_lt_rpow ht0 ht.2 hα
          have hst' : s ^ α < t ^ α := Real.rpow_lt_rpow hs0 hst hα
          apply Summable.tsum_lt_tsum (i := 1)
          · intro k; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hst'.le k) (ha_nn k)
          · simp only [pow_one]; exact mul_lt_mul_of_pos_left hst' a1_pos
          · exact hsumm _ (by positivity) hsX
          · exact hsumm _ (by positivity) htX
        · rintro ⟨f, hf, hfeq⟩
          have : (nhdsWithin r (Set.Ico 0 r)).NeBot := by
            rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hr.ne]
            exact ⟨hr.le, le_rfl⟩
          have h1 : Tendsto f (nhdsWithin r (Set.Ico 0 r)) atTop :=
            hT.congr' (eventually_nhdsWithin_of_forall fun t ht => (hfeq ht).symm)
          exact not_tendsto_nhds_of_tendsto_atTop h1 _ (hf.tendsto.mono_left nhdsWithin_le_nhds)
