-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:28.794999+00:00
-- url     : https://prove2.me/submissions/ee63e212-4d4b-4407-8390-b8883270a606

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Bidding

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- Theorem 10, p. 44. With bidder value fixed at 1 and win/loss feedback, every
randomized measurable policy has worst-case regret Ω(T^(2/3)) against an unknown
i.i.d. distribution of highest competing bids. The bids remain a continuum. -/
theorem solution : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, 0 < T₀ ∧
    ∀ T : ℕ, T₀ ≤ T → ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω), IsProbabilityMeasure μ → ∀ A : BidPolicy Ω, A.IsMeasurable →
      ∃ F : Measure Bid, IsProbabilityMeasure F ∧
        c * (T : ℝ) ^ (2 / 3 : ℝ) ≤
          (T : ℝ) * bidOptimalRevenue F - bidAlgorithmRevenue μ A F T := by
            have twopt : ∀ p e x y : ℝ, 1/4 ≤ p → 0 ≤ e → p + e ≤ 1/2 →
                Real.exp (p * x + (1-p) * y - 16/3 * e^2) ≤ (p+e) * Real.exp x + (1-(p+e)) * Real.exp y
            ·
              intro p e x y hp he hpe
              have hp0 : 0 < p := by linarith
              have hq0 : 0 < 1 - p := by linarith
              have hp1 : 0 < p + e := by linarith
              have hq1 : 0 < 1 - (p + e) := by linarith
              have key := convexOn_exp.2 (Set.mem_univ (x + Real.log ((p+e)/p)))
                (Set.mem_univ (y + Real.log ((1-(p+e))/(1-p)))) hp0.le hq0.le (by ring)
              simp only [smul_eq_mul] at key
              rw [Real.exp_add x, Real.exp_add y, Real.exp_log (by positivity), Real.exp_log (by positivity)] at key
              have e1 : p * (Real.exp x * ((p+e)/p)) + (1-p) * (Real.exp y * ((1-(p+e))/(1-p)))
                  = (p+e) * Real.exp x + (1-(p+e)) * Real.exp y := by
                field_simp
              rw [e1] at key
              refine le_trans (Real.exp_le_exp.2 ?_) key
              have l1 : 1 - p/(p+e) ≤ Real.log ((p+e)/p) := by
                have := Real.one_sub_inv_le_log_of_pos (x := (p+e)/p) (by positivity)
                rwa [inv_div] at this
              have l2 : 1 - (1-p)/(1-(p+e)) ≤ Real.log ((1-(p+e))/(1-p)) := by
                have := Real.one_sub_inv_le_log_of_pos (x := (1-(p+e))/(1-p)) (by positivity)
                rwa [inv_div] at this
              have l3 : -(16/3 * e^2) ≤ p * (1 - p/(p+e)) + (1-p) * (1 - (1-p)/(1-(p+e))) := by
                have : p * (1 - p/(p+e)) + (1-p) * (1 - (1-p)/(1-(p+e))) = - (e^2 / ((p+e)*(1-(p+e)))) := by
                  field_simp
                  ring
                rw [this, neg_le_neg_iff, div_le_iff₀ (by positivity)]
                have h316 : 3/16 ≤ (p+e)*(1-(p+e)) := by
                  have := mul_nonneg (by linarith : 0 ≤ p + e - 1/4) (by linarith : 0 ≤ 3/4 - (p+e))
                  linarith
                have := mul_le_mul_of_nonneg_left h316 (sq_nonneg e)
                linarith
              have k1 := mul_le_mul_of_nonneg_left l1 hp0.le
              have k2 := mul_le_mul_of_nonneg_left l2 hq0.le
              linarith
            have core : ∀ (a : (n:ℕ) → (Fin n → Bid × Bool) → Bid)
                (EH : (Bid → ℝ) → (n:ℕ) → ((Fin n → Bid × Bool) → ℝ) → ℝ)
                (h0 : ∀ p Φ, EH p 0 Φ = Φ Fin.elim0)
                (hS : ∀ p n Φ, EH p (n+1) Φ = EH p n (fun H => p (a n H) * Φ (Fin.snoc H (a n H, true))
                    + (1 - p (a n H)) * Φ (Fin.snoc H (a n H, false))))
                (K T : ℕ) (_ : 6 ≤ K) (_ : 1 ≤ T) (_ : 4 * T ≤ K^3)
                (p0 : Bid → ℝ) (p : Fin K → Bid → ℝ) (χ : Fin K → Bid → ℝ) (Δ : Fin K → ℝ)
                (_ : ∀ b, 0 ≤ p0 b) (_ : ∀ b, p0 b ≤ 1)
                (_ : ∀ j b, χ j b = 0 ∨ (χ j b = 1 ∧ 1/4 ≤ p0 b ∧ p0 b + 1/(4*K) ≤ 1/2))
                (_ : ∀ j b, p j b = p0 b + χ j b * (1/(4*K)))
                (_ : ∀ b, ∑ j, χ j b ≤ 1)
                (_ : ∀ j (b : Bid), (1-(b:ℝ)) * p j b ≤ 1/4 + Δ j * χ j b)
                (_ : ∀ j, 1/(8*K) ≤ Δ j),
                (T:ℝ)/16 ≤ ∑ j, ((T:ℝ) * (1/4 + Δ j) - EH (p j) T
                  (fun H => ∑ t, if (H t).2 then 1 - ((H t).1 : ℝ) else 0))
            ·
              intro a EH h0 hS K T hK hT1 hT p0 p χ Δ hp0 hp1 hχ hp hχs hrev hΔ
              have hK0 : (0:ℝ) < K := by
                have : 0 < K := by omega
                exact_mod_cast this
              have hadd : ∀ q n Φ Ψ, EH q n (fun H => Φ H + Ψ H) = EH q n Φ + EH q n Ψ := by
                intro q n
                induction n with
                | zero => intro Φ Ψ; simp [h0]
                | succ n ih =>
                  intro Φ Ψ
                  rw [hS, hS, hS, ← ih]
                  congr 1; funext H; ring
              have hsmul : ∀ q n (c : ℝ) Φ, EH q n (fun H => c * Φ H) = c * EH q n Φ := by
                intro q n
                induction n with
                | zero => intro c Φ; simp [h0]
                | succ n ih =>
                  intro c Φ
                  rw [hS, hS, ← ih]
                  congr 1; funext H; ring
              have hconst : ∀ q n (c : ℝ), EH q n (fun _ => c) = c := by
                intro q n
                induction n with
                | zero => intro c; simp [h0]
                | succ n ih =>
                  intro c
                  rw [hS]
                  rw [← ih c]
                  congr 1; funext H; rw [ih]; ring
              have hmono : ∀ q, (∀ b, 0 ≤ q b) → (∀ b, q b ≤ 1) → ∀ n Φ Ψ, (∀ H, Φ H ≤ Ψ H) →
                  EH q n Φ ≤ EH q n Ψ := by
                intro q hq0 hq1 n
                induction n with
                | zero => intro Φ Ψ h; simp only [h0]; exact h _
                | succ n ih =>
                  intro Φ Ψ h
                  rw [hS, hS]
                  apply ih
                  intro H
                  exact add_le_add (mul_le_mul_of_nonneg_left (h _) (hq0 _))
                    (mul_le_mul_of_nonneg_left (h _) (by linarith [hq1 (a n H)]))
              have hsum : ∀ q n (Φ : Fin K → (Fin n → Bid × Bool) → ℝ) (s : Finset (Fin K)),
                  EH q n (fun H => ∑ j ∈ s, Φ j H) = ∑ j ∈ s, EH q n (Φ j) := by
                intro q n Φ s
                induction s using Finset.induction_on with
                | empty => simp [hconst]
                | insert i s hi ih =>
                  rw [Finset.sum_insert hi, ← ih, ← hadd]
                  congr 1; funext H; rw [Finset.sum_insert hi]
              have hχ0 : ∀ j b, 0 ≤ χ j b := by
                intro j b; rcases hχ j b with h | h
                · rw [h]
                · rw [h.1]; norm_num
              have hχ1 : ∀ j b, χ j b ≤ 1 := by
                intro j b; rcases hχ j b with h | h
                · rw [h]; norm_num
                · rw [h.1]
              have hpj0 : ∀ j b, 0 ≤ p j b := by
                intro j b; rw [hp]
                have := hp0 b; have := hχ0 j b; positivity
              have hpj1 : ∀ j b, p j b ≤ 1 := by
                intro j b; rw [hp]
                rcases hχ j b with h | h
                · rw [h]; linarith [hp1 b]
                · rw [h.1]; linarith [h.2.2]
              -- count
              let N : Fin K → (n:ℕ) → (Fin n → Bid × Bool) → ℝ := fun j n H => ∑ t, χ j (H t).1
              have hNs : ∀ j n (H : Fin n → Bid × Bool) z, N j (n+1) (Fin.snoc H z) = N j n H + χ j z.1 := by
                intro j n H z
                simp only [N, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
              have hNstep : ∀ q j n, EH q (n+1) (N j (n+1)) = EH q n (fun H => N j n H + χ j (a n H)) := by
                intro q j n
                rw [hS]; congr 1; funext H; rw [hNs, hNs]; ring
              have hN0 : ∀ j n H, 0 ≤ N j n H := fun j n H => Finset.sum_nonneg fun t _ => hχ0 _ _
              have hN1 : ∀ j n H, N j n H ≤ n := by
                intro j n H
                calc N j n H ≤ ∑ t : Fin n, (1:ℝ) := Finset.sum_le_sum fun t _ => hχ1 _ _
                  _ = n := by simp
              let U : (n:ℕ) → (Fin n → Bid × Bool) → ℝ :=
                fun n H => ∑ t, if (H t).2 then 1 - ((H t).1 : ℝ) else 0
              have hUs : ∀ n (H : Fin n → Bid × Bool) z, U (n+1) (Fin.snoc H z) = U n H +
                  (if z.2 then 1 - (z.1 : ℝ) else 0) := by
                intro n H z
                simp only [U, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
              have hR : ∀ j n, EH (p j) n (U n) ≤ n * (1/4) + Δ j * EH (p j) n (N j n) := by
                intro j n
                induction n with
                | zero => simp [h0, U, N]
                | succ n ih =>
                  rw [hNstep, hadd]
                  have e1 : EH (p j) (n+1) (U (n+1)) =
                      EH (p j) n (fun H => U n H + (1 - (a n H : ℝ)) * p j (a n H)) := by
                    rw [hS]; congr 1; funext H; rw [hUs, hUs]; simp; ring
                  rw [e1, hadd]
                  have e2 : EH (p j) n (fun H => (1 - (a n H : ℝ)) * p j (a n H)) ≤
                      EH (p j) n (fun H => 1/4 + Δ j * χ j (a n H)) :=
                    hmono _ (hpj0 j) (hpj1 j) _ _ _ (fun H => hrev _ _)
                  rw [hadd, hconst, hsmul] at e2
                  push_cast
                  linarith
              have hDV : ∀ j (s : ℝ) n (Ψ : (Fin n → Bid × Bool) → ℝ),
                  Real.exp (EH p0 n (fun H => -(s + 16/3 * (1/(4*K))^2) * N j n H + Ψ H)) ≤
                    EH (p j) n (fun H => Real.exp (-s * N j n H + Ψ H)) := by
                intro j s n
                induction n with
                | zero => intro Ψ; simp [h0, N]
                | succ n ih =>
                  intro Ψ
                  have h1 := ih (fun H => -(s + 16/3 * (1/(4*K))^2) * χ j (a n H) +
                    (p0 (a n H) * Ψ (Fin.snoc H (a n H, true)) +
                      (1 - p0 (a n H)) * Ψ (Fin.snoc H (a n H, false))))
                  rw [hS, hS]
                  refine le_trans (le_of_eq ?_) (le_trans h1 ?_)
                  · congr 2; funext H; rw [hNs, hNs]; ring
                  · apply hmono _ (hpj0 j) (hpj1 j)
                    intro H
                    beta_reduce
                    rw [hNs, hNs, hp]
                    beta_reduce
                    set x := Ψ (Fin.snoc H (a n H, true))
                    set y := Ψ (Fin.snoc H (a n H, false))
                    set q := p0 (a n H)
                    set M := N j n H
                    have conv : ∀ z, Real.exp (-s * (M + χ j (a n H)) + z) =
                        Real.exp (-s * M - s * χ j (a n H)) * Real.exp z := by
                      intro z; rw [← Real.exp_add]; congr 1; ring
                    rw [conv, conv]
                    rw [show (q + χ j (a n H) * (1/(4*K))) * (Real.exp (-s * M - s * χ j (a n H)) * Real.exp x)
                      + (1 - (q + χ j (a n H) * (1/(4*K)))) * (Real.exp (-s * M - s * χ j (a n H)) * Real.exp y)
                      = Real.exp (-s * M - s * χ j (a n H)) * ((q + χ j (a n H) * (1/(4*K))) * Real.exp x +
                        (1 - (q + χ j (a n H) * (1/(4*K)))) * Real.exp y) by ring]
                    rw [show -s * M + (-(s + 16/3 * (1/(4*K))^2) * χ j (a n H) + (q * x + (1-q)*y))
                      = (-s * M - s * χ j (a n H)) + (q * x + (1-q)*y - 16/3 * (1/(4*K))^2 * χ j (a n H)) by ring,
                      Real.exp_add]
                    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                    rcases hχ j (a n H) with h | ⟨h, h2, h3⟩
                    · rw [h]
                      have := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) (hp0 (a n H))
                        (by linarith [hp1 (a n H)] : 0 ≤ 1 - q) (by ring)
                      simpa [smul_eq_mul] using this
                    · rw [h]
                      have := twopt q (1/(4*K)) x y h2 (by positivity) h3
                      simpa using this
              have hT0 : (0:ℝ) < T := by exact_mod_cast hT1
              have hfin : ∀ j, EH (p j) T (N j T) ≤
                  2 * (1 + T * (16/3 * (1/(4*K))^2)) * EH p0 T (N j T) := by
                intro j
                have h1 := hDV j (1/T) T (fun _ => 0)
                simp only [add_zero] at h1
                rw [hsmul] at h1
                have h2 : EH (p j) T (fun H => Real.exp (-(1/T) * N j T H)) ≤
                    EH (p j) T (fun H => 1 + (-(1/(2*T))) * N j T H) := by
                  apply hmono _ (hpj0 j) (hpj1 j)
                  intro H
                  beta_reduce
                  have hy0 : 0 ≤ (1/T) * N j T H := mul_nonneg (by positivity) (hN0 _ _ _)
                  have hy1 : (1/T) * N j T H ≤ 1 := by
                    rw [one_div, inv_mul_le_iff₀ hT0, mul_one]; exact hN1 _ _ _
                  rw [show -(1/(T:ℝ)) * N j T H = -((1/T) * N j T H) by ring,
                    show 1 + (-(1/(2*(T:ℝ)))) * N j T H = 1 - ((1/T) * N j T H)/2 by ring]
                  set y := (1/T) * N j T H
                  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by linarith)]
                  refine le_trans ?_ (Real.add_one_le_exp y)
                  rw [inv_le_comm₀ (by linarith) (by linarith)]
                  rw [← one_div, div_le_iff₀ (by linarith)]
                  have := mul_nonneg hy0 (sub_nonneg.2 hy1)
                  linarith
                rw [hadd, hconst, hsmul] at h2
                have h3 := Real.add_one_le_exp (-(1/T + 16/3 * (1/(4*K))^2) * EH p0 T (N j T))
                have h4 : (1/(2*T)) * EH (p j) T (N j T) ≤ (1/T + 16/3 * (1/(4*K))^2) * EH p0 T (N j T) := by
                  linarith
                have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 2 * T)
                have t1 : 2 * (T:ℝ) * (1/(2*T)) = 1 := mul_one_div_cancel (by positivity)
                have t2 : (T:ℝ) * (1/T) = 1 := mul_one_div_cancel hT0.ne'
                rw [← mul_assoc, t1, one_mul] at h5
                refine le_trans h5 (le_of_eq ?_)
                rw [show 2 * (T:ℝ) * ((1/T + 16/3 * (1/(4*K))^2) * EH p0 T (N j T)) =
                  2 * (T * (1/T) + T * (16/3 * (1/(4*K))^2)) * EH p0 T (N j T) by ring, t2]
              have hS0 : ∑ j, EH p0 T (N j T) ≤ T := by
                rw [← hsum]
                calc _ ≤ EH p0 T (fun _ => (T:ℝ)) := by
                      apply hmono _ hp0 hp1
                      intro H
                      simp only [N]
                      rw [Finset.sum_comm]
                      calc _ ≤ ∑ t : Fin T, (1:ℝ) := Finset.sum_le_sum fun t _ => hχs _
                        _ = T := by simp
                  _ = T := hconst _ _ _
              have hSj : ∑ j, EH (p j) T (N j T) ≤ K * T / 2 := by
                calc _ ≤ ∑ j, 2 * (1 + T * (16/3 * (1/(4*K))^2)) * EH p0 T (N j T) :=
                      Finset.sum_le_sum fun j _ => hfin j
                  _ = 2 * (1 + T * (16/3 * (1/(4*K))^2)) * ∑ j, EH p0 T (N j T) := by rw [Finset.mul_sum]
                  _ ≤ 2 * (1 + T * (16/3 * (1/(4*K))^2)) * T := by
                      apply mul_le_mul_of_nonneg_left hS0; positivity
                  _ ≤ (K/2) * T := by
                      apply mul_le_mul_of_nonneg_right _ hT0.le
                      have hTr : 4 * (T:ℝ) ≤ K^3 := by exact_mod_cast hT
                      have hKr : (6:ℝ) ≤ K := by exact_mod_cast hK
                      have : (T:ℝ) * (16/3 * (1/(4*K))^2) ≤ K/12 := by
                        rw [show (T:ℝ) * (16/3 * (1/(4*K))^2) = T / (3 * K^2) by ring]
                        rw [div_le_iff₀ (by positivity), show (K:ℝ)/12 * (3 * K^2) = K^3/4 by ring]
                        linarith
                      linarith
                  _ = _ := by ring
              have hle : ∀ j, EH (p j) T (N j T) ≤ T := by
                intro j
                calc _ ≤ EH (p j) T (fun _ => (T:ℝ)) := hmono _ (hpj0 j) (hpj1 j) _ _ _ (hN1 j T)
                  _ = T := hconst _ _ _
              calc (T:ℝ)/16 = (1/(8*K)) * (K * T - K*T/2) := by field_simp; ring
                _ ≤ (1/(8*K)) * ∑ j : Fin K, (T - EH (p j) T (N j T)) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    rw [Finset.sum_sub_distrib]
                    simp
                    linarith
                _ = ∑ j : Fin K, (1/(8*K)) * (T - EH (p j) T (N j T)) := by rw [Finset.mul_sum]
                _ ≤ _ := by
                    apply Finset.sum_le_sum
                    intro j _
                    have h1 := hR j T
                    have h2 := mul_le_mul_of_nonneg_right (hΔ j) (sub_nonneg.2 (hle j))
                    have h3 : EH (p j) T (U T) = EH (p j) T
                      (fun H => ∑ t, if (H t).2 then 1 - ((H t).1 : ℝ) else 0) := rfl
                    rw [← h3]
                    linarith
            have exEH : ∀ (a : (n:ℕ) → (Fin n → Bid × Bool) → Bid),
                ∃ EH : (Bid → ℝ) → (n:ℕ) → ((Fin n → Bid × Bool) → ℝ) → ℝ,
                  (∀ p Φ, EH p 0 Φ = Φ Fin.elim0) ∧
                  (∀ p n Φ, EH p (n+1) Φ = EH p n (fun H => p (a n H) * Φ (Fin.snoc H (a n H, true))
                    + (1 - p (a n H)) * Φ (Fin.snoc H (a n H, false))))
            ·
              intro a
              exact ⟨fun p n => Nat.rec (motive := fun n => ((Fin n → Bid × Bool) → ℝ) → ℝ)
                (fun Φ => Φ Fin.elim0)
                (fun n ih Φ => ih (fun H => p (a n H) * Φ (Fin.snoc H (a n H, true))
                    + (1 - p (a n H)) * Φ (Fin.snoc H (a n H, false)))) n,
                fun p Φ => rfl, fun p n Φ => rfl⟩
            have histSucc : ∀ {Ω : Type} (A : BidPolicy Ω) (ω : Ω) (h : ℕ → Bid) (n : ℕ),
                bidHistory A ω h (n+1) = Fin.snoc (bidHistory A ω h n)
                  (A n (bidHistory A ω h n) ω, decide ((h n : ℝ) ≤ (A n (bidHistory A ω h n) ω : ℝ)))
            ·
              intro Ω A ω h n
              funext t
              refine Fin.lastCases ?_ (fun t => ?_) t
              · simp [bidHistory]
              · simp [bidHistory]
            have histCongr : ∀ {Ω : Type} (A : BidPolicy Ω) (ω : Ω) (n : ℕ) (h h' : ℕ → Bid),
                (∀ k < n, h k = h' k) → bidHistory A ω h n = bidHistory A ω h' n
            ·
              intro Ω A ω n
              induction n with
              | zero => intro h h' _; rfl
              | succ n ih =>
                intro h h' H
                rw [histSucc, histSucc, ih h h' (fun k hk => H k (by omega)), H n (by omega)]
            have histUtil : ∀ {Ω : Type} (A : BidPolicy Ω) (ω : Ω) (h : ℕ → Bid) (n : ℕ),
                (∑ t : Fin n, if (bidHistory A ω h n t).2 then 1 - ((bidHistory A ω h n t).1 : ℝ) else 0)
                  = ∑ t : Fin n, bidUtility (A t (bidHistory A ω h t) ω) (h t)
            ·
              intro Ω A ω h n
              induction n with
              | zero => simp
              | succ n ih =>
                rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, histSucc]
                simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
                rw [ih]
                simp [bidUtility, auctionUtility]
            have conv : ∀ {Ω : Type} (A : BidPolicy Ω) (ω : Ω)
                (EH : (Bid → ℝ) → (n:ℕ) → ((Fin n → Bid × Bool) → ℝ) → ℝ)
                (h0 : ∀ p Φ, EH p 0 Φ = Φ Fin.elim0)
                (hS : ∀ p n Φ, EH p (n+1) Φ = EH p n (fun H => p (A n H ω) * Φ (Fin.snoc H (A n H ω, true))
                    + (1 - p (A n H ω)) * Φ (Fin.snoc H (A n H ω, false))))
                (m : ℕ) (x : Fin m → Bid) (w : Fin m → ℝ) (_ : ∑ i, w i = 1) (d : Bid) (n : ℕ)
                (Φ : (Fin n → Bid × Bool) → ℝ),
                ∑ g : Fin n → Fin m, (∏ t, w (g t)) *
                  Φ (bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n) =
                EH (fun b => ∑ i, w i * if (x i : ℝ) ≤ (b:ℝ) then 1 else 0) n Φ
            ·
              intro Ω A ω EH h0 hS m x w hw d n
              induction n with
              | zero =>
                intro Φ
                rw [h0]
                simp [bidHistory]
              | succ n ih =>
                intro Φ
                rw [hS, ← ih, ← (Fin.snocEquiv (fun _ : Fin (n+1) => Fin m)).sum_comp, Fintype.sum_prod_type,
                  Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro g _
                have e1 : ∀ i : Fin m, bidHistory A ω (fun k => if hk : k < n+1 then
                    x ((Fin.snocEquiv (fun _ : Fin (n+1) => Fin m)) (i, g) ⟨k, hk⟩) else d) (n+1) =
                    Fin.snoc (bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n)
                    (A n (bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n) ω,
                     decide ((x i : ℝ) ≤ (A n (bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n) ω : ℝ))) := by
                  intro i
                  rw [histSucc]
                  have e2 : bidHistory A ω (fun k => if hk : k < n+1 then
                    x ((Fin.snocEquiv (fun _ : Fin (n+1) => Fin m)) (i, g) ⟨k, hk⟩) else d) n =
                    bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n := by
                    apply histCongr
                    intro k hk
                    have hk' : k < n + 1 := by omega
                    simp only [hk, hk', dif_pos, Fin.snocEquiv_apply]
                    congr 1
                    exact Fin.snoc_castSucc (α := fun _ => Fin m) i g ⟨k, hk⟩
                  rw [e2]
                  have e3 : (Fin.snocEquiv (fun _ : Fin (n+1) => Fin m)) (i, g) ⟨n, by omega⟩ = i := by
                    rw [Fin.snocEquiv_apply]
                    exact Fin.snoc_last (α := fun _ => Fin m) i g
                  simp only [Nat.lt_succ_self, dif_pos, e3]
                have e4 : ∀ i : Fin m, ∏ t, w ((Fin.snocEquiv (fun _ : Fin (n+1) => Fin m)) (i, g) t) =
                    (∏ t, w (g t)) * w i := by
                  intro i
                  rw [Fin.prod_univ_castSucc]
                  simp only [Fin.snocEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last]
                simp only [e1, e4]
                set H := bidHistory A ω (fun k => if hk : k < n then x (g ⟨k, hk⟩) else d) n
                set b := A n H ω
                simp only [mul_assoc]
                rw [← Finset.mul_sum]
                congr 1
                have e5 : 1 - ∑ i, w i * (if (x i : ℝ) ≤ (b:ℝ) then (1:ℝ) else 0) =
                    ∑ i, w i * (if (x i : ℝ) ≤ (b:ℝ) then (0:ℝ) else 1) := by
                  rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
                  refine hw.symm.trans ?_
                  apply Finset.sum_congr rfl
                  intro i _
                  split_ifs <;> simp
                rw [e5, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                split_ifs with hc <;> simp [hc]
            have meas : ∀ (m : ℕ) (x : Fin m → Bid) (w : Fin m → ℝ) (_ : Function.Injective x)
                (_ : ∀ i, 0 ≤ w i) (_ : ∑ i, w i = 1),
                ∃ F : Measure Bid, IsProbabilityMeasure F ∧ (∀ G : Bid → ℝ, ∫ h, G h ∂F = ∑ i, w i * G (x i)) ∧
                  ∀ (T : ℕ) (G : (Fin T → Bid) → ℝ), ∫ h, G h ∂(Measure.pi (fun _ : Fin T => F)) =
                    ∑ g : Fin T → Fin m, (∏ t, w (g t)) * G (fun t => x (g t))
            ·
              intro m x w hx hw0 hw1
              let P : PMF (Fin m) := PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
                rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one])
              have hP : ∀ i, P.toMeasure.real {i} = w i := by
                intro i
                rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
                simp [P, hw0 i]
              have emb1 : MeasurableEmbedding x :=
                ⟨hx, measurable_of_finite _, fun {s} _ => (s.toFinite.image _).measurableSet⟩
              have hpr : IsProbabilityMeasure (Measure.map x P.toMeasure) :=
                Measure.isProbabilityMeasure_map emb1.measurable.aemeasurable
              refine ⟨Measure.map x P.toMeasure, hpr, ?_, ?_⟩
              · intro G
                rw [emb1.integral_map, integral_fintype Integrable.of_finite]
                simp [hP]
              · intro T G
                have emb2 : MeasurableEmbedding (fun (g : Fin T → Fin m) t => x (g t)) :=
                  ⟨fun g g' h => funext fun t => hx (congrFun h t), measurable_of_finite _,
                    fun {s} _ => (s.toFinite.image _).measurableSet⟩
                rw [← Measure.pi_map_pi (fun _ => emb1.measurable.aemeasurable), emb2.integral_map,
                  integral_fintype Integrable.of_finite]
                apply Finset.sum_congr rfl
                intro g _
                rw [smul_eq_mul]
                congr 1
                rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
                exact Finset.prod_congr rfl fun t _ => hP _
            have inst : ∀ (K : ℕ) (_ : 6 ≤ K), ∃ (x : Fin (K+2) → Bid) (w : Fin K → Fin (K+2) → ℝ)
                (p0 : Bid → ℝ) (χ : Fin K → Bid → ℝ) (Δ : Fin K → ℝ) (β : Fin K → Bid),
                Function.Injective x ∧ (∀ j i, 0 ≤ w j i) ∧ (∀ j, ∑ i, w j i = 1) ∧
                (∀ b, 0 ≤ p0 b) ∧ (∀ b, p0 b ≤ 1) ∧
                (∀ j b, χ j b = 0 ∨ (χ j b = 1 ∧ 1/4 ≤ p0 b ∧ p0 b + 1/(4*K) ≤ 1/2)) ∧
                (∀ j (b:Bid), (∑ i, w j i * if (x i : ℝ) ≤ (b:ℝ) then 1 else 0) = p0 b + χ j b * (1/(4*K))) ∧
                (∀ b, ∑ j, χ j b ≤ 1) ∧
                (∀ j (b : Bid), (1-(b:ℝ)) * (∑ i, w j i * if (x i : ℝ) ≤ (b:ℝ) then 1 else 0)
                  ≤ 1/4 + Δ j * χ j b) ∧
                (∀ j, 1/(8*K) ≤ Δ j) ∧
                (∀ j, 1/4 + Δ j ≤ (1-(β j:ℝ)) * (∑ i, w j i * if (x i : ℝ) ≤ (β j:ℝ) then 1 else 0))
            ·
              intro K hK
              have hK0 : (0:ℝ) < K := by
                have : 0 < K := by omega
                exact_mod_cast this
              obtain ⟨xr, hxr⟩ : ∃ xr : ℕ → ℝ, xr = fun i => if i ≤ K then (i:ℝ)/(K+i) else 1 := ⟨_, rfl⟩
              obtain ⟨w0, hw0⟩ : ∃ w0 : ℕ → ℝ, w0 = fun i => if i = 0 then (1/4:ℝ) else if i ≤ K then 1/(4*(K:ℝ)) else 1/2 :=
                ⟨_, rfl⟩
              have xle : ∀ i, i ≤ K → xr i = (i:ℝ)/(K+i) := by intro i hi; simp [hxr, hi]
              have xK1 : xr (K+1) = 1 := by simp [hxr]
              have x0 : ∀ i, 0 ≤ xr i := by
                intro i; rw [hxr]; beta_reduce; split_ifs <;> positivity
              have x1 : ∀ i, xr i ≤ 1 := by
                intro i; rw [hxr]; beta_reduce; split_ifs
                · rw [div_le_one (by positivity)]; linarith
                · exact le_rfl
              have xhalf : ∀ i, i ≤ K → xr i ≤ 1/2 := by
                intro i hi
                have : (i:ℝ) ≤ K := by exact_mod_cast hi
                rw [xle i hi, div_le_iff₀ (by positivity)]; linarith
              have xm : ∀ i k, i < k → k ≤ K + 1 → xr i < xr k := by
                intro i k hik hk
                rcases Nat.lt_or_ge K k with h | h
                · have : k = K+1 := by omega
                  rw [this, xK1]
                  have := xhalf i (by omega)
                  linarith
                · rw [xle i (by omega), xle k h, div_lt_div_iff₀ (by positivity) (by positivity)]
                  have : (i:ℝ) < k := by exact_mod_cast hik
                  nlinarith
              have xmle : ∀ i k, i ≤ k → k ≤ K + 1 → xr i ≤ xr k := by
                intro i k hik hk
                rcases Nat.eq_or_lt_of_le hik with h | h
                · rw [h]
                · exact (xm i k h hk).le
              have w0nn : ∀ i, 0 ≤ w0 i := by
                intro i; rw [hw0]; beta_reduce; split_ifs <;> positivity
              have wL : ∀ n, n ≤ K → ∑ i ∈ Finset.range (n+1), w0 i = ((K:ℝ)+n)/(4*K) := by
                intro n
                induction n with
                | zero => intro _; simp [hw0]; field_simp
                | succ n ih =>
                  intro hn
                  rw [Finset.sum_range_succ, ih (by omega)]
                  have : w0 (n+1) = 1/(4*K) := by simp [hw0, hn]
                  rw [this]; push_cast; field_simp; ring
              have w01 : ∑ i ∈ Finset.range (K+2), w0 i = 1 := by
                rw [Finset.sum_range_succ, wL K le_rfl]
                have : w0 (K+1) = 1/2 := by simp [hw0]
                rw [this]; field_simp; norm_num
              obtain ⟨P0, hP0⟩ : ∃ P0 : ℝ → ℝ, P0 = fun b => ∑ i ∈ Finset.range (K+2), w0 i * if xr i ≤ b then 1 else 0 :=
                ⟨_, rfl⟩
              have Pj : ∀ j b, j ≤ K → xr j ≤ b → b < xr (j+1) → P0 b = ((K:ℝ)+j)/(4*K) := by
                intro j b hj h1 h2
                rw [← wL j hj, hP0]
                beta_reduce
                have hsub : Finset.range (j+1) ⊆ Finset.range (K+2) := Finset.range_mono (by omega)
                rw [← Finset.sum_subset hsub (f := fun i => w0 i * if xr i ≤ b then 1 else 0)]
                · apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.mem_range] at hi
                  rw [if_pos (le_trans (xmle i j (by omega) (by omega)) h1), mul_one]
                · intro i hi hi'
                  rw [Finset.mem_range] at hi hi'
                  rw [if_neg (not_le.2 (lt_of_lt_of_le h2 (xmle (j+1) i (by omega) (by omega)))), mul_zero]
              have exj : ∀ b, 0 ≤ b → b < 1 → ∃ j, j ≤ K ∧ xr j ≤ b ∧ b < xr (j+1) := by
                intro b hb0 hb1
                have hx00 : xr 0 ≤ b := by rw [xle 0 (by omega)]; simpa using hb0
                refine ⟨Nat.findGreatest (fun j => xr j ≤ b) K, Nat.findGreatest_le _,
                  Nat.findGreatest_spec (P := fun j => xr j ≤ b) (Nat.zero_le K) hx00, ?_⟩
                rcases Nat.eq_or_lt_of_le (Nat.findGreatest_le (P := fun j => xr j ≤ b) K) with h | h
                · rw [h, xK1]; exact hb1
                · exact not_le.1 (Nat.findGreatest_is_greatest (P := fun j => xr j ≤ b) (Nat.lt_succ_self _) h)
              have uniq : ∀ i j b, i ≤ K → j ≤ K → xr i ≤ b → b < xr (i+1) → xr j ≤ b → b < xr (j+1) → i = j := by
                intro i j b hi hj h1 h2 h3 h4
                by_contra hne
                rcases Nat.lt_or_gt_of_ne hne with h | h
                · linarith [xmle (i+1) j h (by omega)]
                · linarith [xmle (j+1) i h (by omega)]
              have P0nn : ∀ b, 0 ≤ P0 b := by
                intro b; rw [hP0]
                refine Finset.sum_nonneg fun i _ => mul_nonneg (w0nn i) ?_
                split_ifs <;> norm_num
              have P01 : ∀ b, P0 b ≤ 1 := by
                intro b; rw [hP0]
                refine le_trans (Finset.sum_le_sum fun i _ => ?_) w01.le
                split_ifs
                · rw [mul_one]
                · rw [mul_zero]; exact w0nn i
              obtain ⟨wr, hwr⟩ : ∃ wr : ℕ → ℕ → ℝ, wr = fun j i => w0 i + (1/(4*K)) * (if i = j then 1 else 0)
                  - (1/(4*K)) * (if i = j+1 then 1 else 0) := ⟨_, rfl⟩
              have wrnn : ∀ j i, j < K → 0 ≤ wr j i := by
                intro j i hj
                rw [hwr]; beta_reduce
                by_cases h : i = j + 1
                · have h1 : i ≠ j := by omega
                  have h2 : w0 i = 1/(4*K) := by
                    rw [h]; simp [hw0]; omega
                  rw [h2]; simp [h]
                · rw [if_neg h]
                  have := w0nn i
                  split_ifs
                  · have : (0:ℝ) ≤ 1/(4*K) := by positivity
                    linarith
                  · linarith
              have wrsum : ∀ j (f : ℕ → ℝ), j < K → ∑ i ∈ Finset.range (K+2), wr j i * f i =
                  (∑ i ∈ Finset.range (K+2), w0 i * f i) + (1/(4*K)) * f j - (1/(4*K)) * f (j+1) := by
                intro j f hj
                have e : ∀ i, wr j i * f i = w0 i * f i + (if i = j then (1/(4*(K:ℝ))) * f i else 0)
                    - (if i = j+1 then (1/(4*(K:ℝ))) * f i else 0) := by
                  intro i; rw [hwr]; beta_reduce; split_ifs <;> ring
                rw [Finset.sum_congr rfl (fun i _ => e i)]
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
                  if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))]
              obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ → ℝ, c = fun j b => if xr j ≤ b ∧ b < xr (j+1) then 1 else 0 := ⟨_, rfl⟩
              have hPj : ∀ j b, j < K → ∑ i ∈ Finset.range (K+2), wr j i * (if xr i ≤ b then 1 else 0) =
                  P0 b + c j b * (1/(4*K)) := by
                intro j b hj
                rw [wrsum j (fun i => if xr i ≤ b then 1 else 0) hj, hP0, hc]
                beta_reduce
                have := xm j (j+1) (by omega) (by omega)
                by_cases h1 : xr j ≤ b
                · by_cases h2 : xr (j+1) ≤ b
                  · simp [h1, h2, not_lt.2 h2]
                  · simp [h1, h2, not_le.1 h2]
                · have h2 : ¬ xr (j+1) ≤ b := by linarith
                  simp [h1, h2]
              have hfin : ∀ j b, (∑ i : Fin (K+2), wr j i * (if xr i ≤ b then 1 else 0)) =
                  ∑ i ∈ Finset.range (K+2), wr j i * (if xr i ≤ b then 1 else 0) := by
                intro j b
                exact Fin.sum_univ_eq_sum_range (fun i => wr j i * (if xr i ≤ b then 1 else 0)) (K+2)
              have hc01 : ∀ j b, c j b = 0 ∨ c j b = 1 := by
                intro j b; rw [hc]; beta_reduce; split_ifs <;> simp
              have hc1 : ∀ j b, c j b = 1 → xr j ≤ b ∧ b < xr (j+1) := by
                intro j b; rw [hc]; beta_reduce; intro h
                by_contra hne
                rw [if_neg hne] at h
                norm_num at h
              have hid : ∀ j, j ≤ K → (1 - xr j) * (((K:ℝ)+j)/(4*K)) = 1/4 := by
                intro j hj
                rw [xle j hj]
                have : (0:ℝ) < K + j := by positivity
                field_simp
                ring
              refine ⟨fun i => ⟨xr i, x0 i, x1 i⟩, fun j i => wr j i, fun b => P0 b, fun j b => c j b,
                fun j => (1 - xr j) * (1/(4*K)), fun j => ⟨xr j, x0 j, x1 j⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro i k h
                have h' : xr i = xr k := congrArg Subtype.val h
                by_contra hne
                have hne' : (i:ℕ) ≠ k := fun h => hne (Fin.ext h)
                rcases Nat.lt_or_gt_of_ne hne' with h | h
                · linarith [xm i k h (by omega)]
                · linarith [xm k i h (by omega)]
              · intro j i; exact wrnn j i j.2
              · intro j
                have := wrsum j (fun _ => 1) j.2
                rw [Fin.sum_univ_eq_sum_range (fun i => wr j i) (K+2)]
                simp only [mul_one] at this
                rw [this, w01]; ring
              · intro b; exact P0nn b
              · intro b; exact P01 b
              · intro j b
                rcases hc01 j b with h | h
                · exact Or.inl h
                · refine Or.inr ⟨h, ?_⟩
                  obtain ⟨h1, h2⟩ := hc1 j b h
                  have hj : ((j:ℕ):ℝ) + 1 ≤ K := by exact_mod_cast j.2
                  have hj0 : (0:ℝ) ≤ ((j:ℕ):ℝ) := by positivity
                  beta_reduce
                  rw [Pj j b (by omega) h1 h2]
                  constructor
                  · rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
                  · rw [← add_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
              · intro j b
                exact (hfin j b).trans (hPj j b j.2)
              · intro b
                by_cases h : ∃ j : Fin K, c j b = 1
                · obtain ⟨j, hj⟩ := h
                  rw [Finset.sum_eq_single j]
                  · exact hj.le
                  · intro i _ hij
                    rcases hc01 i b with h | h
                    · exact h
                    · exfalso
                      obtain ⟨h1, h2⟩ := hc1 i b h
                      obtain ⟨h3, h4⟩ := hc1 j b hj
                      exact hij (Fin.ext (uniq i j b (by omega) (by omega) h1 h2 h3 h4))
                  · simp
                · push Not at h
                  rw [Finset.sum_eq_zero]
                  · norm_num
                  · intro i _
                    exact (hc01 i b).resolve_right (h i)
              · intro j b
                have e := (hfin j b).trans (hPj j b j.2)
                refine le_trans (le_of_eq (congrArg (fun z => (1-(b:ℝ)) * z) e)) ?_
                beta_reduce
                have hb0 : 0 ≤ (b:ℝ) := b.2.1
                have hb1 : (b:ℝ) ≤ 1 := b.2.2
                have part1 : (1-(b:ℝ)) * P0 b ≤ 1/4 := by
                  rcases hb1.lt_or_eq with h | h
                  · obtain ⟨k, hk, h1, h2⟩ := exj b hb0 h
                    rw [Pj k b hk h1 h2, ← hid k hk]
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    linarith
                  · rw [h]; norm_num
                have part2 : (1-(b:ℝ)) * (c j b * (1/(4*K))) ≤ (1 - xr j) * (1/(4*K)) * c j b := by
                  rcases hc01 j b with h | h
                  · rw [h]; simp
                  · rw [h]
                    obtain ⟨h1, h2⟩ := hc1 j b h
                    have : (1-(b:ℝ)) * (1/(4*K)) ≤ (1 - xr j) * (1/(4*K)) :=
                      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                    linarith
                linarith
              · intro j
                have := xhalf j (by omega)
                have h2 : (1/2) * (1/(4*(K:ℝ))) ≤ (1 - xr j) * (1/(4*K)) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                refine le_trans (le_of_eq ?_) h2
                field_simp
                norm_num
              · intro j
                have e := (hfin j (xr j)).trans (hPj j (xr j) j.2)
                refine le_trans (le_of_eq ?_) (le_of_eq (congrArg (fun z => (1-xr j) * z) e).symm)
                beta_reduce
                have hlt := xm j (j+1) (by omega) (by omega)
                have hc' : c j (xr j) = 1 := by rw [hc]; simp [hlt]
                rw [hc', Pj j (xr j) (by omega) le_rfl hlt, mul_add, hid j (by omega)]
                ring
            refine ⟨1/64, by norm_num, 54, by norm_num, ?_⟩
            intro T hT Ω _ μ hμ A hA
            have hTr : (54:ℝ) ≤ T := by exact_mod_cast hT
            have hT0 : (0:ℝ) < T := by linarith
            -- choice of K
            obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (T:ℝ) ^ (1/3 : ℝ) := ⟨_, rfl⟩
            have hy0 : 0 < y := by rw [hy]; positivity
            have hy3 : y^3 = T := by
              rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
            have hy2 : (T:ℝ) ^ (2/3 : ℝ) = y^2 := by
              rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
            have hy37 : 3 ≤ y := by
              by_contra h
              push Not at h
              have : y^3 < 3^3 := pow_lt_pow_left₀ h hy0.le (by norm_num)
              linarith
            obtain ⟨K, hKd⟩ : ∃ K : ℕ, K = ⌈2 * y⌉₊ := ⟨_, rfl⟩
            have hK1 : 2 * y ≤ K := by rw [hKd]; exact Nat.le_ceil _
            have hK2 : (K:ℝ) ≤ 4 * y := by
              have := Nat.ceil_lt_add_one (a := 2*y) (by positivity)
              rw [← hKd] at this
              linarith
            have hK6 : 6 ≤ K := by
              have : (6:ℝ) ≤ K := by linarith
              exact_mod_cast this
            have hK0 : (0:ℝ) < K := by linarith
            have hKT : 4 * T ≤ K^3 := by
              have : (2*y)^3 ≤ (K:ℝ)^3 := pow_le_pow_left₀ (by positivity) hK1 3
              have : 4 * (T:ℝ) ≤ K^3 := by
                rw [← hy3]
                have e : (2*y)^3 = 8 * y^3 := by ring
                have := pow_pos hy0 3
                linarith
              exact_mod_cast this
            obtain ⟨x, w, p0, χ, Δ, β, hx, hw0, hw1, hp0, hp1, hχ, hp, hχs, hrev, hΔ, hβ⟩ := inst K hK6
            choose F hF hF1 hF2 using fun j => meas (K+2) x (w j) hx (hw0 j) (hw1 j)
            have hb01 : ∀ b h : Bid, 0 ≤ bidUtility b h ∧ bidUtility b h ≤ 1 := by
              intro b h
              have h1 : 0 ≤ (b:ℝ) := b.2.1
              have h2 : (b:ℝ) ≤ 1 := b.2.2
              unfold bidUtility auctionUtility
              split_ifs
              · constructor <;> simp <;> linarith
              · norm_num
            have hrevF : ∀ j b, bidRevenue (F j) b =
                (1-(b:ℝ)) * ∑ i, w j i * if (x i : ℝ) ≤ (b:ℝ) then 1 else 0 := by
              intro j b
              unfold bidRevenue
              rw [hF1, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp only [bidUtility, auctionUtility]
              split_ifs <;> ring
            have hopt : ∀ j, 1/4 + Δ j ≤ bidOptimalRevenue (F j) := by
              intro j
              refine le_trans (hβ j) ?_
              rw [← hrevF j (β j)]
              refine le_csSup ⟨1, ?_⟩ ⟨β j, rfl⟩
              rintro _ ⟨b, rfl⟩
              unfold bidRevenue
              rw [hF1, ← hw1 j]
              refine Finset.sum_le_sum fun i _ => ?_
              have := mul_le_mul_of_nonneg_left (hb01 b (x i)).2 (hw0 j i)
              linarith
            have hΔ0 : ∀ j, 0 ≤ Δ j := fun j => le_trans (by positivity) (hΔ j)
            have hc0 : 1/64 * (T:ℝ)^(2/3:ℝ) ≤ T * (1/4) := by
              rw [hy2, ← hy3]
              have e : y^2 * (1/64) ≤ y^2 * (y * (1/4)) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              linarith
            obtain ⟨f, hf⟩ : ∃ f : Ω × (Fin T → Bid) → ℝ, f = fun z =>
              let h : ℕ → Bid := fun n => if hn : n < T then z.2 ⟨n, hn⟩ else ⟨0, by norm_num⟩
              ∑ t : Fin T, bidUtility (A t (bidHistory A z.1 h t) z.1) (h t) := ⟨_, rfl⟩
            have hAlg : ∀ j, bidAlgorithmRevenue μ A (F j) T =
                ∫ z, f z ∂(μ.prod (Measure.pi (fun _ : Fin T => F j))) := by
              intro j; rw [hf]; rfl
            by_cases hint : ∀ j, Integrable f (μ.prod (Measure.pi (fun _ : Fin T => F j)))
            · -- main case
              have hinner : ∀ ω, (T:ℝ)/16 ≤ ∑ j, ((T:ℝ) * (1/4 + Δ j) -
                  ∫ h, f (ω, h) ∂(Measure.pi (fun _ : Fin T => F j))) := by
                intro ω
                obtain ⟨EH, h0, hS⟩ := exEH (fun n H => A n H ω)
                have := core (fun n H => A n H ω) EH h0 hS K T hK6 (by omega) hKT p0
                  (fun j b => ∑ i, w j i * if (x i : ℝ) ≤ (b:ℝ) then 1 else 0) χ Δ hp0 hp1 hχ hp hχs hrev hΔ
                refine le_trans this (le_of_eq ?_)
                apply Finset.sum_congr rfl
                intro j _
                congr 1
                rw [hF2, ← conv A ω EH h0 hS (K+2) x (w j) (hw1 j) ⟨0, by norm_num⟩ T]
                apply Finset.sum_congr rfl
                intro g _
                congr 1
                rw [histUtil, hf]
              have hsum : (T:ℝ)/16 ≤ ∑ j, ((T:ℝ) * (1/4 + Δ j) - bidAlgorithmRevenue μ A (F j) T) := by
                have hI : ∀ j, Integrable (fun ω => ∫ h, f (ω, h) ∂(Measure.pi (fun _ : Fin T => F j))) μ :=
                  fun j => (hint j).integral_prod_left
                have hI2 : ∀ j ∈ Finset.univ, Integrable (fun ω => (T:ℝ) * (1/4 + Δ j) -
                    ∫ h, f (ω, h) ∂(Measure.pi (fun _ : Fin T => F j))) μ :=
                  fun j _ => (integrable_const _).sub (hI j)
                have h1 := integral_mono (integrable_const ((T:ℝ)/16)) (integrable_finsetSum _ hI2) hinner
                rw [integral_finsetSum _ hI2] at h1
                simp only [integral_const, probReal_univ, one_smul] at h1
                refine le_trans h1 (le_of_eq ?_)
                apply Finset.sum_congr rfl
                intro j _
                rw [integral_sub (integrable_const _) (hI j), hAlg, integral_prod _ (hint j)]
                simp
              have hex : ∃ j : Fin K, (T:ℝ)/(16*K) ≤ (T:ℝ) * (1/4 + Δ j) - bidAlgorithmRevenue μ A (F j) T := by
                by_contra hcon
                push Not at hcon
                have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
                have h2 := Finset.sum_lt_sum_of_nonempty hne (fun j _ => hcon j)
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
                have : (K:ℝ) * (T/(16*K)) = T/16 := by field_simp
                linarith
              obtain ⟨j, hj⟩ := hex
              refine ⟨F j, hF j, ?_⟩
              have h1 := mul_le_mul_of_nonneg_left (hopt j) hT0.le
              have h2 : 1/64 * (T:ℝ)^(2/3:ℝ) ≤ T/(16*K) := by
                rw [hy2, le_div_iff₀ (by positivity), ← hy3]
                have := mul_le_mul_of_nonneg_left hK2 (by positivity : 0 ≤ y^2)
                linarith
              linarith
            · push Not at hint
              obtain ⟨j, hj⟩ := hint
              refine ⟨F j, hF j, ?_⟩
              rw [hAlg, integral_undef hj, sub_zero]
              have h1 := mul_le_mul_of_nonneg_left (hopt j) hT0.le
              have h2 := mul_nonneg hT0.le (hΔ0 j)
              linarith
