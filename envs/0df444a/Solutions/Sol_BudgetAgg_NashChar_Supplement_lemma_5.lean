-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:02.13871+00:00
-- url     : https://prove2.me/submissions/8bdbe855-d862-4637-95a3-af10e09d31f0

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 5, p. 28: with `ℓ∞` preferences, `m = 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem solution {n : ℕ} (hn : 3 ≤ n) (f : Mechanism n 3) :
    ¬ (IsEfficientMech lInfUtil f ∧ IsStrategyproofFor lInfUtil f ∧ IsProportional f) := by
      rintro ⟨hE, hS, hP⟩
      have hF3 : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      have hsum : ∀ q : stdSimplex ℝ (Fin 3), q.1 0 + q.1 1 + q.1 2 = 1 := by
        intro q; have := q.2.2; rw [Fin.sum_univ_three] at this; exact this
      have hnn : ∀ (q : stdSimplex ℝ (Fin 3)) j, 0 ≤ q.1 j := fun q j => q.2.1 j
      have hmk : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c = 1 →
          ∃ p : stdSimplex ℝ (Fin 3), p.1 0 = a ∧ p.1 1 = b ∧ p.1 2 = c := by
        intro a b c ha hb hc h
        refine ⟨⟨![a, b, c], ?_, ?_⟩, rfl, rfl, rfl⟩
        · intro j; rcases hF3 j with rfl|rfl|rfl <;> simpa
        · rw [Fin.sum_univ_three]; simpa using h
      have hlowL : ∀ (p q : stdSimplex ℝ (Fin 3)) (j : Fin 3),
          lInfUtil p q ≤ p.1 j - q.1 j ∧ lInfUtil p q ≤ q.1 j - p.1 j := by
        intro p q j
        have h : lInfUtil p q ≤ -|p.1 j - q.1 j| := by
          unfold lInfUtil
          exact neg_le_neg (Finset.le_sup' (fun j => |p.1 j - q.1 j|) (Finset.mem_univ j))
        constructor
        · linarith [neg_abs_le (p.1 j - q.1 j), neg_le_abs (p.1 j - q.1 j)]
        · linarith [neg_abs_le (p.1 j - q.1 j), le_abs_self (p.1 j - q.1 j)]
      have hU : ∀ (p q : stdSimplex ℝ (Fin 3)) (T : ℝ),
          p.1 0 - q.1 0 ≤ T → q.1 0 - p.1 0 ≤ T → p.1 1 - q.1 1 ≤ T → q.1 1 - p.1 1 ≤ T →
          p.1 2 - q.1 2 ≤ T → q.1 2 - p.1 2 ≤ T → -T ≤ lInfUtil p q := by
        intro p q T a b c d e g
        unfold lInfUtil
        rw [neg_le_neg_iff]
        apply Finset.sup'_le
        intro j _
        rcases hF3 j with rfl|rfl|rfl <;> rw [abs_le] <;> constructor <;> linarith
      have hUS : ∀ (p q : stdSimplex ℝ (Fin 3)) (T : ℝ),
          p.1 0 - q.1 0 < T → q.1 0 - p.1 0 < T → p.1 1 - q.1 1 < T → q.1 1 - p.1 1 < T →
          p.1 2 - q.1 2 < T → q.1 2 - p.1 2 < T → -T < lInfUtil p q := by
        intro p q T a b c d e g
        unfold lInfUtil
        rw [neg_lt_neg_iff, Finset.sup'_lt_iff]
        intro j _
        rcases hF3 j with rfl|rfl|rfl <;> rw [abs_lt] <;> constructor <;> linarith
      have hN : (3:ℝ) ≤ n := by exact_mod_cast hn
      have hN0 : (n:ℝ) ≠ 0 := by positivity
      obtain ⟨t, ht⟩ : ∃ u : ℝ, u = 1 / (4 * (n:ℝ)) := ⟨_, rfl⟩
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / ((n:ℝ) + 1) := ⟨_, rfl⟩
      have htpos : 0 < t := by rw [ht]; positivity
      have ht3 : 12 * t ≤ 1 := by
        rw [ht, mul_one_div, div_le_one (by positivity)]; linarith
      have hst : s < 4 * t := by
        rw [hs, ht, show 4 * (1 / (4 * (n:ℝ))) = 1 / n by field_simp]
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      have hst2 : 3 * t ≤ s := by
        rw [hs, ht, show 3 * (1 / (4 * (n:ℝ))) = 3 / (4 * n) by ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      obtain ⟨eA, hA0, hA1, hA2⟩ := hmk 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨eB, hB0, hB1, hB2⟩ := hmk 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨eC, hC0, hC1, hC2⟩ := hmk 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨x, hx0, hx1, hx2⟩ := hmk (6*t) (1 - 6*t) 0 (by linarith) (by linarith) le_rfl (by ring)
      obtain ⟨z, hz0, hz1, hz2⟩ := hmk 0 (1 - 6*t) (6*t) le_rfl (by linarith) (by linarith) (by ring)
      obtain ⟨y, hy0, hy1, hy2⟩ := hmk s (1 - s) 0 (by linarith) (by linarith) le_rfl (by ring)
      obtain ⟨y', hy'0, hy'1, hy'2⟩ := hmk 0 (1 - s) s le_rfl (by linarith) (by linarith) (by ring)
      obtain ⟨i0, hi0⟩ : ∃ i : Fin n, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
      obtain ⟨iL, hiL⟩ : ∃ i : Fin n, i.val = n - 1 := ⟨⟨n-1, by omega⟩, rfl⟩
      obtain ⟨im, him⟩ : ∃ i : Fin n, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
      have hL0 : iL ≠ i0 := fun h => by rw [h] at hiL; omega
      have hm0 : im ≠ i0 := fun h => by rw [h] at him; omega
      have hmL : im ≠ iL := fun h => by rw [h] at him; omega
      obtain ⟨Prof, hP0, hPL, hPm⟩ : ∃ Prof : stdSimplex ℝ (Fin 3) → stdSimplex ℝ (Fin 3) → Profile n 3,
          (∀ p r, Prof p r i0 = p) ∧ (∀ p r, Prof p r iL = r) ∧
          (∀ p r k, k ≠ i0 → k ≠ iL → Prof p r k = eB) :=
        ⟨fun p r k => if k = i0 then p else if k = iL then r else eB, by simp,
          by intro p r; simp [hL0], by intro p r k h1 h2; simp [h1, h2]⟩
      have hSP0 : ∀ p p' r, lInfUtil p (f (Prof p' r)) ≤ lInfUtil p (f (Prof p r)) := by
        intro p p' r
        have := hS i0 (Prof p r) (Prof p' r) (by
          intro k hk
          by_cases hkL : k = iL
          · rw [hkL, hPL, hPL]
          · rw [hPm _ _ _ hk hkL, hPm _ _ _ hk hkL])
        rwa [hP0] at this
      have hSPL : ∀ p r r', lInfUtil r (f (Prof p r')) ≤ lInfUtil r (f (Prof p r)) := by
        intro p r r'
        have := hS iL (Prof p r) (Prof p r') (by
          intro k hk
          by_cases hk0 : k = i0
          · rw [hk0, hP0, hP0]
          · rw [hPm _ _ _ hk0 hk, hPm _ _ _ hk0 hk])
        rwa [hPL] at this
      have hEff : ∀ p r (q' : stdSimplex ℝ (Fin 3)),
          lInfUtil p (f (Prof p r)) ≤ lInfUtil p q' → lInfUtil r (f (Prof p r)) ≤ lInfUtil r q' →
          lInfUtil eB (f (Prof p r)) < lInfUtil eB q' → False := by
        intro p r q' h0 hL hm
        apply hE (Prof p r)
        refine ⟨q', fun k => ?_, im, ?_⟩
        · by_cases hk0 : k = i0
          · rw [hk0, hP0]; exact h0
          by_cases hkL : k = iL
          · rw [hkL, hPL]; exact hL
          rw [hPm _ _ _ hk0 hkL]; exact hm.le
        · rw [hPm _ _ _ hm0 hmL]; exact hm
      have hsumN : ∀ g : Fin n → ℝ, (∀ k, k ≠ i0 → k ≠ iL → g k = g im) →
          ∑ k, g k = g i0 + g iL + ((n:ℝ) - 2) * g im := by
        intro g hg
        have hmem : iL ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hL0, Finset.mem_univ iL⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ← Finset.add_sum_erase _ _ hmem]
        rw [Finset.sum_congr rfl (fun k hk => hg k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
          (Finset.mem_erase.mp hk).1)]
        rw [Finset.sum_const, Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show n - 1 - 1 = n - 2 by omega, Nat.cast_sub (by omega)]
        push_cast; ring
      have hprop : ∀ p r (j : Fin 3), (∀ j, p.1 j = 0 ∨ p.1 j = 1) → (∀ j, r.1 j = 0 ∨ r.1 j = 1) →
          (f (Prof p r)).1 j = (p.1 j + r.1 j + ((n:ℝ) - 2) * eB.1 j) / n := by
        intro p r j hp hr
        have hsm : IsSingleMinded (Prof p r) := by
          intro k j'
          by_cases h0 : k = i0
          · rw [h0, hP0]; exact hp j'
          by_cases hL : k = iL
          · rw [hL, hPL]; exact hr j'
          rw [hPm _ _ _ h0 hL]; rcases hF3 j' with rfl|rfl|rfl <;> simp [hB0, hB1, hB2]
        rw [hP (Prof p r) hsm j, hsumN (fun k => (Prof p r k).1 j)
          (fun k h0 hL => by simp only [hPm _ _ _ h0 hL, hPm _ _ _ hm0 hmL])]
        simp only [hP0, hPL, hPm _ _ _ hm0 hmL]
      have smA : ∀ j, eA.1 j = 0 ∨ eA.1 j = 1 := by
        intro j; rcases hF3 j with rfl|rfl|rfl <;> simp [hA0, hA1, hA2]
      have smB : ∀ j, eB.1 j = 0 ∨ eB.1 j = 1 := by
        intro j; rcases hF3 j with rfl|rfl|rfl <;> simp [hB0, hB1, hB2]
      have smC : ∀ j, eC.1 j = 0 ∨ eC.1 j = 1 := by
        intro j; rcases hF3 j with rfl|rfl|rfl <;> simp [hC0, hC1, hC2]
      have hvA : ∀ q, lInfUtil eA q = q.1 0 - 1 := by
        intro q; have := hsum q; have := hnn q 0; have := hnn q 1; have := hnn q 2
        apply le_antisymm
        · have := (hlowL eA q 0).2; linarith
        · have := hU eA q (1 - q.1 0) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
      have hvB : ∀ q, lInfUtil eB q = q.1 1 - 1 := by
        intro q; have := hsum q; have := hnn q 0; have := hnn q 1; have := hnn q 2
        apply le_antisymm
        · have := (hlowL eB q 1).2; linarith
        · have := hU eB q (1 - q.1 1) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
      have hvC : ∀ q, lInfUtil eC q = q.1 2 - 1 := by
        intro q; have := hsum q; have := hnn q 0; have := hnn q 1; have := hnn q 2
        apply le_antisymm
        · have := (hlowL eC q 2).2; linarith
        · have := hU eC q (1 - q.1 2) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
      have hq2a : (f (Prof eA eC)).1 0 = (4*t) := by
        rw [hprop _ _ _ smA smC, hA0, hC0, hB0, ht]; field_simp; ring
      have hq2b : (f (Prof eA eC)).1 1 = 1 - 8 * t := by
        rw [hprop _ _ _ smA smC, hA1, hC1, hB1, ht]; field_simp; ring
      have hq2c : (f (Prof eA eC)).1 2 = (4*t) := by
        rw [hprop _ _ _ smA smC, hA2, hC2, hB2, ht]; field_simp; ring
      have hq4b : (f (Prof eB eC)).1 1 = 1 - (4*t) := by
        rw [hprop _ _ _ smB smC, hB1, hC1, ht]; field_simp; ring
      have hq4b' : (f (Prof eA eB)).1 1 = 1 - (4*t) := by
        rw [hprop _ _ _ smA smB, hB1, hA1, ht]; field_simp; ring

      clear hA0 hA1 hA2 hB0 hB1 hB2 hC0 hC1 hC2 hi0 hiL him hL0 hm0 hmL hP0 hPL hPm hN hN0 ht hs
        hF3 hS hE hP hprop hsumN smA smB smC hn
      -- Part A: profile 1 = Prof x eC
      have partA : 1 - 6*t ≤ (f (Prof x eC)).1 1 ∧ 3*t < (f (Prof x eC)).1 2 ∧
          (f (Prof x eC)).1 2 ≤ (4*t) := by
        have s1 := hsum (f (Prof x eC)); have n10 := hnn (f (Prof x eC)) 0
        have n11 := hnn (f (Prof x eC)) 1; have n12 := hnn (f (Prof x eC)) 2
        have A1 : -(4*t) ≤ lInfUtil x (f (Prof x eC)) := by
          have h1 := hSP0 x eA eC
          have h2 := hU x (f (Prof eA eC)) (4*t) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
        obtain ⟨-, A1a⟩ := hlowL x (f (Prof x eC)) 0
        obtain ⟨A1c, -⟩ := hlowL x (f (Prof x eC)) 2
        have A2 : (f (Prof x eC)).1 0 ≤ (4*t) := by
          have := hSP0 eA x eC; rw [hvA, hvA] at this; linarith
        have A3 : 1 - 6*t ≤ (f (Prof x eC)).1 1 := by
          by_contra hcon; rw [not_le] at hcon
          obtain ⟨q', h0, h1, h2⟩ := hmk (6*t - (f (Prof x eC)).1 2) (1 - 6*t) ((f (Prof x eC)).1 2)
            (by linarith) (by linarith) n12 (by ring)
          apply hEff x eC q'
          · have := (hlowL x (f (Prof x eC)) 2).1
            have := hU x q' ((f (Prof x eC)).1 2) (by linarith) (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith)
            linarith
          · rw [hvC, hvC, h2]
          · rw [hvB, hvB, h1]; linarith
        refine ⟨A3, ?_, by linarith⟩
        by_contra hcon; rw [not_lt] at hcon
        have hy3 : -(3*t) ≤ lInfUtil y (f (Prof y eC)) := by
          have h1 := hSP0 y x eC
          have h2 := hU y (f (Prof x eC)) (3*t) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
        clear A1 A1a A1c A2 A3 s1 n10 n11 n12 hcon
        have s3 := hsum (f (Prof y eC)); have n30 := hnn (f (Prof y eC)) 0
        have n31 := hnn (f (Prof y eC)) 1; have n32 := hnn (f (Prof y eC)) 2
        have h3 := (hlowL y (f (Prof y eC)) 2).1
        have hc3 : (f (Prof y eC)).1 2 ≤ 3*t := by linarith
        have hb3 : 1 - s ≤ (f (Prof y eC)).1 1 := by
          by_contra hcon2; rw [not_le] at hcon2
          obtain ⟨q', g0, g1, g2⟩ := hmk (s - (f (Prof y eC)).1 2) (1 - s) ((f (Prof y eC)).1 2)
            (by linarith) (by linarith) n32 (by ring)
          apply hEff y eC q'
          · have := hU y q' ((f (Prof y eC)).1 2) (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
            linarith
          · rw [hvC, hvC, g2]
          · rw [hvB, hvB, g1]; linarith
        have h4 := hSP0 eB y eC
        rw [hvB, hvB] at h4; linarith
      -- Part B: profile 5 = Prof eA z
      have partB : 1 - 6*t ≤ (f (Prof eA z)).1 1 ∧ 3*t < (f (Prof eA z)).1 0 ∧
          (f (Prof eA z)).1 0 ≤ (4*t) := by
        clear partA
        have s5 := hsum (f (Prof eA z)); have n50 := hnn (f (Prof eA z)) 0
        have n51 := hnn (f (Prof eA z)) 1; have n52 := hnn (f (Prof eA z)) 2
        have B1 : -(4*t) ≤ lInfUtil z (f (Prof eA z)) := by
          have h1 := hSPL eA z eC
          have h2 := hU z (f (Prof eA eC)) (4*t) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
        obtain ⟨B1a, -⟩ := hlowL z (f (Prof eA z)) 0
        obtain ⟨-, B1c⟩ := hlowL z (f (Prof eA z)) 2
        have B2 : (f (Prof eA z)).1 2 ≤ (4*t) := by
          have := hSPL eA eC z; rw [hvC, hvC] at this; linarith
        have B3 : 1 - 6*t ≤ (f (Prof eA z)).1 1 := by
          by_contra hcon; rw [not_le] at hcon
          obtain ⟨q', h0, h1, h2⟩ := hmk ((f (Prof eA z)).1 0) (1 - 6*t) (6*t - (f (Prof eA z)).1 0)
            n50 (by linarith) (by linarith) (by ring)
          apply hEff eA z q'
          · rw [hvA, hvA, h0]
          · have := (hlowL z (f (Prof eA z)) 0).1
            have := hU z q' ((f (Prof eA z)).1 0) (by linarith) (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith)
            linarith
          · rw [hvB, hvB, h1]; linarith
        refine ⟨B3, ?_, by linarith⟩
        by_contra hcon; rw [not_lt] at hcon
        have hy3 : -(3*t) ≤ lInfUtil y' (f (Prof eA y')) := by
          have h1 := hSPL eA y' z
          have h2 := hU y' (f (Prof eA z)) (3*t) (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
          linarith
        clear B1 B1a B1c B2 B3 s5 n50 n51 n52 hcon
        have s3 := hsum (f (Prof eA y')); have n30 := hnn (f (Prof eA y')) 0
        have n31 := hnn (f (Prof eA y')) 1; have n32 := hnn (f (Prof eA y')) 2
        have h3 := (hlowL y' (f (Prof eA y')) 0).1
        have hc3 : (f (Prof eA y')).1 0 ≤ 3*t := by linarith
        have hb3 : 1 - s ≤ (f (Prof eA y')).1 1 := by
          by_contra hcon2; rw [not_le] at hcon2
          obtain ⟨q', g0, g1, g2⟩ := hmk ((f (Prof eA y')).1 0) (1 - s) (s - (f (Prof eA y')).1 0)
            n30 (by linarith) (by linarith) (by ring)
          apply hEff eA y' q'
          · rw [hvA, hvA, g0]
          · have := hU y' q' ((f (Prof eA y')).1 0) (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
            linarith
          · rw [hvB, hvB, g1]; linarith
        have h4 := hSPL eA eB y'
        rw [hvB, hvB] at h4; linarith
      -- Final: profile 6 = Prof x z
      obtain ⟨A3, A4, A5⟩ := partA
      obtain ⟨B3, B4, B5⟩ := partB
      have s1 := hsum (f (Prof x eC)); have n10 := hnn (f (Prof x eC)) 0
      have s5 := hsum (f (Prof eA z)); have n52 := hnn (f (Prof eA z)) 2
      have F1 := hUS z (f (Prof x eC)) (3*t) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)
      have F2 := hSPL x z eC
      have F3 := (hlowL z (f (Prof x z)) 0).1
      have F5 := hUS x (f (Prof eA z)) (3*t) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)
      have F6 := hSP0 x eA z
      have F7 := (hlowL x (f (Prof x z)) 0).2
      linarith
