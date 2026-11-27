-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:35.96314+00:00
-- url     : https://prove2.me/submissions/97976c16-b140-416c-9bc6-8563c3a53041

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hA1 : Assumption1 P π m ρ) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a), (b): a non-increasing step-size sequence α₀ ≥ ⋯ ≥ α_T with α_T > 0
    (∀ (T : ℕ) (α : ℕ → ℝ), (∀ i j, i ≤ j → j ≤ T → α j ≤ α i) → 0 < α T →
      (∀ t : ℕ, 2 * tauMixLam m ρ (γ * lam) (α T) < t → t ≤ T →
        pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
            (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
            (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (1 + 2 * (tauMixLam m ρ (γ * lam) (α T) : ℝ))
              * α (t - 2 * tauMixLam m ρ (γ * lam) (α T))) ∧
      (∀ t : ℕ, t ≤ 2 * tauMixLam m ρ (γ * lam) (α T) → t ≤ T →
        pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
            (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
            (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (1 + 2 * (tauMixLam m ρ (γ * lam) (α T) : ℝ)) * α 0
            + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t)) ∧
    -- (c): every t, any nonnegative step sizes
    (∀ α : ℕ → ℝ, (∀ i, 0 ≤ α i) → ∀ t : ℕ,
      pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
          (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
          (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
        ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * ∑ i ∈ Finset.range t, α i
          + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t) := by
            classical
            have hne : Nonempty S := by
              by_contra h
              rw [not_nonempty_iff] at h
              have := hπ.2.1
              simp at this
            obtain ⟨s0⟩ := hne
            have hr0 : 0 ≤ rmax := le_trans (abs_nonneg _) (hRw s0 s0)
            have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
            have hq0' : 0 ≤ γ * lam := mul_nonneg hγ0 hlam0
            have hq1' : γ * lam < 1 := (mul_le_of_le_one_right hγ0 hlam1).trans_lt hγ1
            obtain ⟨q, hq⟩ : ∃ q, q = γ * lam := ⟨_, rfl⟩
            rw [← hq] at hq0' hq1'
            have hq0 : 0 ≤ q := hq0'
            have hq1 : q < 1 := hq1'
            have h1q : 0 < 1 - q := by linarith
            obtain ⟨M, hM⟩ : ∃ M, M = rmax + 2 * R := ⟨_, rfl⟩
            obtain ⟨B, hB⟩ : ∃ B, B = M / (1 - q) := ⟨_, rfl⟩
            have hM0 : 0 ≤ M := by rw [hM]; linarith
            have hBq : B * (1 - q) = M := by rw [hB]; field_simp
            have hB0 : 0 ≤ B := by rw [hB]; positivity
            have hMB : M ≤ B := by
              rw [← hBq]; exact mul_le_of_le_one_right hB0 (by linarith)
            have hRM : 2 * R ≤ M := by rw [hM]; linarith
            -- powers of P
            obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → S → S → ℝ, ∀ k s y, Q k s y = (Matrix.of P ^ k) s y :=
              ⟨fun k s y => (Matrix.of P ^ k) s y, fun _ _ _ => rfl⟩
            have hQ0 : ∀ s y, Q 0 s y = if s = y then 1 else 0 := by
              intro s y; rw [hQ, pow_zero, Matrix.one_apply]
            have hQs : ∀ k s y, Q (k + 1) s y = ∑ z, Q k s z * P z y := by
              intro k s y; rw [hQ, pow_succ, Matrix.mul_apply]; simp [hQ]
            have hQnn : ∀ k s y, 0 ≤ Q k s y := by
              intro k
              induction k with
              | zero => intro s y; rw [hQ0]; split_ifs <;> norm_num
              | succ k ih =>
                intro s y; rw [hQs]
                exact Finset.sum_nonneg fun z _ => mul_nonneg (ih s z) (hP.1 z y)
            have hQ1 : ∀ k s, ∑ y, Q k s y = 1 := by
              intro k
              induction k with
              | zero => intro s; simp [hQ0]
              | succ k ih =>
                intro s; simp_rw [hQs]
                rw [Finset.sum_comm]
                simp_rw [← Finset.mul_sum, hP.2, mul_one]
                exact ih s
            have hπQ : ∀ k y, ∑ s, π s * Q k s y = π y := by
              intro k
              induction k with
              | zero => intro s; simp [hQ0]
              | succ k ih =>
                intro y; simp_rw [hQs, Finset.mul_sum]
                rw [Finset.sum_comm]
                simp_rw [← mul_assoc, ← Finset.sum_mul, ih]
                exact hπ.2.2 y
            -- averages
            have havg : ∀ (p v : S → ℝ) (c : ℝ), (∀ s, 0 ≤ p s) → ∑ s, p s = 1 → (∀ s, |v s| ≤ c) →
                |∑ s, p s * v s| ≤ c := by
              intro p v c hp h1 hv
              calc |∑ s, p s * v s| ≤ ∑ s, |p s * v s| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ s, p s * c := by
                  apply Finset.sum_le_sum
                  intro s _
                  rw [abs_mul, abs_of_nonneg (hp s)]
                  exact mul_le_mul_of_nonneg_left (hv s) (hp s)
                _ = c := by rw [← Finset.sum_mul, h1, one_mul]
            have havgE : ∀ (p : S → ℝ) (v : S → ℝ) (c : ℝ), (∀ s, 0 ≤ p s) → ∑ s, p s = 1 →
                (∀ s, |v s| ≤ c) → ‖∑ s, (p s * v s) • φ s‖ ≤ c := by
              intro p v c hp h1 hv
              calc ‖∑ s, (p s * v s) • φ s‖ ≤ ∑ s, ‖(p s * v s) • φ s‖ := norm_sum_le _ _
                _ ≤ ∑ s, p s * c := by
                  apply Finset.sum_le_sum
                  intro s _
                  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp s)]
                  have h2 : p s * |v s| ≤ p s * c := mul_le_mul_of_nonneg_left (hv s) (hp s)
                  have h3 : 0 ≤ p s * |v s| := mul_nonneg (hp s) (abs_nonneg _)
                  exact (mul_le_of_le_one_right h3 (hφ s)).trans h2
                _ = c := by rw [← Finset.sum_mul, h1, one_mul]
            -- resolvent tail
            have htail : ∀ (v : S → ℝ) (c : ℝ), (∀ x, |v x| ≤ c) → ∀ s,
                Summable (fun k => q ^ k * ∑ y, Q k s y * v y) ∧
                ∀ N, |(∑' k, q ^ k * ∑ y, Q k s y * v y) - ∑ k ∈ Finset.range N, q ^ k * ∑ y, Q k s y * v y|
                  ≤ c * q ^ N / (1 - q) := by
              intro v c hv s
              have hb : ∀ k, ‖q ^ k * ∑ y, Q k s y * v y‖ ≤ q ^ k * c := by
                intro k
                rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 k)]
                exact mul_le_mul_of_nonneg_left (havg _ v c (hQnn k s) (hQ1 k s) hv) (pow_nonneg hq0 k)
              have hgs := (summable_geometric_of_lt_one hq0 hq1).mul_right c
              have hs : Summable (fun k => q ^ k * ∑ y, Q k s y * v y) := Summable.of_norm_bounded hgs hb
              refine ⟨hs, fun N => ?_⟩
              rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left, ← Real.norm_eq_abs]
              have hg : HasSum (fun k => q ^ (k + N) * c) (c * q ^ N / (1 - q)) := by
                have := ((hasSum_geometric_of_lt_one hq0 hq1).mul_right (q ^ N * c))
                have e1 : (fun k => q ^ (k + N) * c) = fun k => q ^ k * (q ^ N * c) := by
                  funext k; rw [pow_add]; ring
                have e2 : c * q ^ N / (1 - q) = (1 - q)⁻¹ * (q ^ N * c) := by
                  rw [div_eq_mul_inv]; ring
                rw [e1, e2]; exact this
              exact tsum_of_norm_bounded hg (fun k => hb (k + N))
            -- the mean TD error
            obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin d) → S → ℝ, ∀ θ x, u θ x =
                ∑ x', P x x' * (Rw x x' + γ * valFn φ θ x' - valFn φ θ x) := ⟨_, fun _ _ => rfl⟩
            have hinn : ∀ s θ, |inner ℝ (φ s) θ| ≤ ‖θ‖ := by
              intro s θ
              calc |inner ℝ (φ s) θ| ≤ ‖φ s‖ * ‖θ‖ := abs_real_inner_le_norm _ _
                _ ≤ 1 * ‖θ‖ := mul_le_mul_of_nonneg_right (hφ s) (norm_nonneg _)
                _ = ‖θ‖ := one_mul _
            have hδ : ∀ θ s s', ‖θ‖ ≤ R → |tdErr γ Rw φ θ s s'| ≤ M := by
              intro θ s s' hθ
              unfold tdErr
              have h1 := abs_le.1 (hRw s s')
              have h2 := abs_le.1 (hinn s θ)
              have h3 : |γ * inner ℝ (φ s') θ| ≤ R := by
                rw [abs_mul, abs_of_nonneg hγ0]
                exact (mul_le_of_le_one_left (abs_nonneg _) hγ1.le).trans ((hinn s' θ).trans hθ)
              have h4 := abs_le.1 h3
              rw [hM, abs_le]
              constructor
              · linarith [h1.1, h2.2, h4.1]
              · linarith [h1.2, h2.1, h4.2]
            have hδL : ∀ θ θ' s s', |tdErr γ Rw φ θ s s' - tdErr γ Rw φ θ' s s'| ≤ 2 * ‖θ - θ'‖ := by
              intro θ θ' s s'
              unfold tdErr
              have h2 := abs_le.1 (hinn s (θ - θ'))
              have h3 : |γ * inner ℝ (φ s') (θ - θ')| ≤ ‖θ - θ'‖ := by
                rw [abs_mul, abs_of_nonneg hγ0]
                exact (mul_le_of_le_one_left (abs_nonneg _) hγ1.le).trans (hinn s' _)
              have h4 := abs_le.1 h3
              rw [inner_sub_right] at h2 h4
              rw [mul_sub] at h4
              rw [abs_le]
              constructor
              · linarith [h2.2, h4.1]
              · linarith [h2.1, h4.2]
            have hutd : ∀ θ x, u θ x = ∑ x', P x x' * tdErr γ Rw φ θ x x' := by
              intro θ x; rw [hu]; rfl
            have huM : ∀ θ, ‖θ‖ ≤ R → ∀ x, |u θ x| ≤ M := by
              intro θ hθ x
              rw [hutd]
              exact havg _ _ _ (hP.1 x) (hP.2 x) (fun s => hδ θ x s hθ)
            have huL : ∀ θ θ' x, |u θ x - u θ' x| ≤ 2 * ‖θ - θ'‖ := by
              intro θ θ' x
              rw [hutd, hutd, ← Finset.sum_sub_distrib]
              simp_rw [← mul_sub]
              exact havg _ _ _ (hP.1 x) (hP.2 x) (fun s => hδL θ θ' x s)
            -- xbar
            obtain ⟨X, hX⟩ : ∃ X, X = xbar π P γ lam Rw φ := ⟨_, rfl⟩
            have hXe : ∀ θ, X θ = ∑ s, (π s * ∑' k, q ^ k * ∑ y, Q k s y * u θ y) • φ s := by
              intro θ
              rw [hX, xbar, gbarH]
              apply Finset.sum_congr rfl
              intro s _
              congr 2
              rw [Tlam, add_sub_cancel_left]
              apply tsum_congr
              intro k
              rw [← hq]
              congr 1
              rw [Matrix.mulVec, dotProduct]
              apply Finset.sum_congr rfl
              intro y _
              rw [hQ, hu]
            have hXB : ∀ θ, ‖θ‖ ≤ R → ‖X θ‖ ≤ B := by
              intro θ hθ
              rw [hXe]
              apply havgE _ _ _ hπ.1 hπ.2.1
              intro s
              have := (htail (u θ) M (huM θ hθ) s).2 0
              simpa [← hB] using this
            have hXL : ∀ θ θ', ‖X θ - X θ'‖ ≤ 2 * ‖θ - θ'‖ / (1 - q) := by
              intro θ θ'
              rw [hXe, hXe, ← Finset.sum_sub_distrib]
              simp_rw [← sub_smul, ← mul_sub]
              apply havgE _ _ _ hπ.1 hπ.2.1
              intro s
              obtain ⟨c1, hc1⟩ : ∃ c, ∀ x, |u θ x| ≤ c :=
                ⟨∑ x, |u θ x|, fun x => Finset.single_le_sum (f := fun x => |u θ x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)⟩
              obtain ⟨c2, hc2⟩ : ∃ c, ∀ x, |u θ' x| ≤ c :=
                ⟨∑ x, |u θ' x|, fun x => Finset.single_le_sum (f := fun x => |u θ' x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)⟩
              rw [← (htail _ c1 hc1 s).1.tsum_sub (htail _ c2 hc2 s).1]
              have := (htail (fun x => u θ x - u θ' x) _ (huL θ θ') s).2 0
              simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one] at this
              have e : ∀ k, (q ^ k * ∑ y, Q k s y * u θ y - q ^ k * ∑ y, Q k s y * u θ' y)
                  = q ^ k * ∑ y, Q k s y * (u θ y - u θ' y) := by
                intro k
                rw [← mul_sub, ← Finset.sum_sub_distrib]
                simp_rw [mul_sub]
              rw [tsum_congr e]
              exact this
            -- truncation bias
            obtain ⟨D, hD⟩ : ∃ D : ℕ → EuclideanSpace ℝ (Fin d) → S → ℝ, ∀ k θ y, D k θ y =
                inner ℝ (φ y) (θ - θstar) * ∑ z, Q k y z * u θ z := ⟨_, fun _ _ _ => rfl⟩
            have hdiff : ∀ θ, ‖θ‖ ≤ R → ‖θ - θstar‖ ≤ 2 * R := by
              intro θ hθ
              have := norm_sub_le θ θstar
              linarith
            have hDb : ∀ k θ y, ‖θ‖ ≤ R → |D k θ y| ≤ M * M := by
              intro k θ y hθ
              rw [hD, abs_mul]
              apply mul_le_mul _ _ (abs_nonneg _) hM0
              · exact (hinn _ _).trans ((hdiff θ hθ).trans hRM)
              · exact havg _ _ _ (hQnn k y) (hQ1 k y) (huM θ hθ)
            have htrunc : ∀ θ N, ‖θ‖ ≤ R →
                |(∑ k ∈ Finset.range N, q ^ k * ∑ y, π y * D k θ y) - inner ℝ (X θ) (θ - θstar)|
                  ≤ M * M * q ^ N / (1 - q) := by
              intro θ N hθ
              have h1 : (∑ k ∈ Finset.range N, q ^ k * ∑ y, π y * D k θ y) - inner ℝ (X θ) (θ - θstar)
                  = - ∑ s, π s * (inner ℝ (φ s) (θ - θstar) * ((∑' k, q ^ k * ∑ y, Q k s y * u θ y)
                    - ∑ k ∈ Finset.range N, q ^ k * ∑ y, Q k s y * u θ y)) := by
                rw [hXe, sum_inner]
                simp_rw [real_inner_smul_left, hD, Finset.mul_sum (Finset.univ : Finset S)]
                rw [Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro s _
                rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum, neg_sub]
                congr 1
                · apply Finset.sum_congr rfl
                  intro k _
                  simp_rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro z _
                  ring
                · ring
              rw [h1, abs_neg]
              apply havg _ _ _ hπ.1 hπ.2.1
              intro s
              rw [abs_mul]
              have h2 := (htail (u θ) M (huM θ hθ) s).2 N
              have h3 : |inner ℝ (φ s) (θ - θstar)| ≤ M := (hinn _ _).trans ((hdiff θ hθ).trans hRM)
              calc _ ≤ M * (M * q ^ N / (1 - q)) := mul_le_mul h3 h2 (abs_nonneg _) hM0
                _ = _ := by ring
            -- path expectations
            obtain ⟨E, hE⟩ : ∃ E : ℕ → ((ℕ → S) → ℝ) → ℝ, ∀ n F, E n F =
              ∑ w : Fin (n + 1) → S, pathProb π P n w * F (extendPath w) := ⟨_, fun _ _ => rfl⟩
            have hpnn : ∀ n w, 0 ≤ pathProb π P n w := by
              intro n w
              exact mul_nonneg (hπ.1 _) (Finset.prod_nonneg fun i _ => hP.1 _ _)
            have hEadd : ∀ n F G, E n (fun w => F w + G w) = E n F + E n G := by
              intro n F G
              rw [hE, hE, hE, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun w _ => by ring
            have hEsub : ∀ n F G, E n (fun w => F w - G w) = E n F - E n G := by
              intro n F G
              rw [hE, hE, hE, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun w _ => by ring
            have hEsum : ∀ n N (c : ℕ → ℝ) (F : ℕ → (ℕ → S) → ℝ),
                E n (fun w => ∑ k ∈ Finset.range N, c k * F k w) = ∑ k ∈ Finset.range N, c k * E n (F k) := by
              intro n N c F
              simp_rw [hE, Finset.mul_sum]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => by ring
            have hEmono : ∀ n F G, (∀ w, F w ≤ G w) → E n F ≤ E n G := by
              intro n F G h
              rw [hE, hE]
              exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h _) (hpnn n w)
            have hE0 : ∀ f : S → ℝ, E 0 (fun w => f (w 0)) = ∑ s, π s * f s := by
              intro f
              rw [hE, ← (Equiv.funUnique (Fin 1) S).sum_comp]
              apply Finset.sum_congr rfl
              intro w _
              simp [pathProb, extendPath]
            have hstep : ∀ n (C : (ℕ → S) → S → ℝ), (∀ w w', (∀ i ≤ n, w i = w' i) → C w = C w') →
                E (n + 1) (fun w => C w (w (n + 1))) = E n (fun w => ∑ x, P (w n) x * C w x) := by
              intro n C hC
              rw [hE, hE, ← (Fin.snocEquiv (fun _ : Fin (n + 2) => S)).sum_comp, Fintype.sum_prod_type,
                Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              have hw : ∀ j : Fin (n + 1), (Fin.snocEquiv (fun _ : Fin (n + 2) => S)) (x, v) j.castSucc = v j := by
                intro j; simp [Fin.snocEquiv]
              have hl : (Fin.snocEquiv (fun _ : Fin (n + 2) => S)) (x, v) (Fin.last (n + 1)) = x := by
                simp [Fin.snocEquiv]
              obtain ⟨W, hW⟩ : ∃ W : Fin (n + 2) → S, W = (Fin.snocEquiv (fun _ : Fin (n + 2) => S)) (x, v) :=
                ⟨_, rfl⟩
              rw [← hW] at hw hl ⊢
              have e1 : C (extendPath W) = C (extendPath v) := by
                apply hC
                intro i hi
                have := hw ⟨i, by omega⟩
                simp only [extendPath]
                convert this using 2
                · ext; simp; omega
                · ext; simp; omega
              have e2 : extendPath W (n + 1) = x := by
                rw [← hl]
                simp only [extendPath]
                congr 1
                ext; simp
              have e3 : extendPath v n = v (Fin.last n) := by
                simp only [extendPath]
                congr 1
                ext; simp
              have e4 : pathProb π P (n + 1) W = pathProb π P n v * P (v (Fin.last n)) x := by
                unfold pathProb
                rw [Fin.prod_univ_castSucc, ← mul_assoc]
                congr 1
                · congr 1
                  · rw [← hw 0]; rfl
                  · apply Finset.prod_congr rfl
                    intro i _
                    rw [hw, Fin.succ_castSucc, hw]
                · rw [hw, Fin.succ_last, hl]
              rw [e1, e2, e3, e4]
              ring
            have hmulti : ∀ j a (C : (ℕ → S) → S → ℝ), (∀ w w', (∀ i ≤ a, w i = w' i) → C w = C w') →
                E (a + j) (fun w => C w (w (a + j))) = E a (fun w => ∑ x, Q j (w a) x * C w x) := by
              intro j
              induction j with
              | zero =>
                intro a C hC
                congr 1
                ext w
                simp [hQ0]
              | succ j ih =>
                intro a C hC
                rw [← add_assoc, hstep (a + j) C (fun w w' h => hC w w' (fun i hi => h i (by omega))),
                  ih a (fun w y => ∑ x, P y x * C w x)
                    (fun w w' h => by ext y; rw [hC w w' h])]
                congr 1
                ext w
                simp_rw [hQs, Finset.mul_sum, Finset.sum_mul]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
            have hmarg : ∀ j a (F : (ℕ → S) → ℝ), (∀ w w', (∀ i ≤ a, w i = w' i) → F w = F w') →
                E (a + j) F = E a F := by
              intro j a F hF
              have := hmulti j a (fun w _ => F w) (fun w w' h => by rw [hF w w' h])
              simp only [← Finset.sum_mul, hQ1, one_mul] at this
              exact this
            have hEconst : ∀ n (c : ℝ), E n (fun _ => c) = c := by
              intro n c
              have h1 := hmarg n 0 (fun _ => c) (fun _ _ _ => rfl)
              rw [zero_add] at h1
              rw [h1, hE0 (fun _ => c), ← Finset.sum_mul, hπ.2.1, one_mul]
            have hEabs : ∀ n F c, (∀ w, |F w| ≤ c) → |E n F| ≤ c := by
              intro n F c h
              rw [abs_le]
              constructor
              · rw [← hEconst n (-c)]
                exact hEmono n _ _ fun w => (abs_le.1 (h w)).1
              · rw [← hEconst n c]
                exact hEmono n _ _ fun w => (abs_le.1 (h w)).2
            -- zeta
            obtain ⟨Z, hZ⟩ : ∃ Z : EuclideanSpace ℝ (Fin d) → (ℕ → S) → ℕ → ℝ, ∀ θ w t, Z θ w t =
              zetaLam π P γ lam Rw φ θstar θ (traceN φ q w t) (w t) (w (t + 1)) := ⟨_, fun _ _ _ => rfl⟩
            have hZe : ∀ θ w t, Z θ w t = inner ℝ (tdErr γ Rw φ θ (w t) (w (t + 1)) • traceN φ q w t - X θ)
                (θ - θstar) := by
              intro θ w t; rw [hZ, hX]; rfl
            have hgeo : ∀ n, ∑ k ∈ Finset.range n, q ^ k ≤ 1 / (1 - q) := by
              intro n
              rw [geom_sum_eq (ne_of_lt hq1), ← neg_div_neg_eq, neg_sub, neg_sub]
              apply div_le_div_of_nonneg_right _ h1q.le
              have := pow_nonneg hq0 n
              linarith
            have htr : ∀ w t, ‖traceN φ q w t‖ ≤ 1 / (1 - q) := by
              intro w t
              refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun k _ => ?_) (hgeo (t + 1)))
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 k)]
              exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
            have hg : ∀ θ w t, ‖θ‖ ≤ R → ‖tdErr γ Rw φ θ (w t) (w (t + 1)) • traceN φ q w t‖ ≤ B := by
              intro θ w t hθ
              rw [norm_smul, Real.norm_eq_abs, hB, div_eq_mul_one_div]
              exact mul_le_mul (hδ _ _ _ hθ) (htr w t) (norm_nonneg _) hM0
            have hLip : ∀ θ θ' w t, ‖θ‖ ≤ R → ‖θ'‖ ≤ R → Z θ w t ≤ Z θ' w t + 6 * B * ‖θ - θ'‖ := by
              intro θ θ' w t hθ hθ'
              rw [hZe, hZe]
              obtain ⟨z, hz⟩ : ∃ z, z = traceN φ q w t := ⟨_, rfl⟩
              obtain ⟨a, ha⟩ : ∃ a, a = tdErr γ Rw φ θ (w t) (w (t + 1)) := ⟨_, rfl⟩
              obtain ⟨b, hb⟩ : ∃ b, b = tdErr γ Rw φ θ' (w t) (w (t + 1)) := ⟨_, rfl⟩
              have h1 : ‖a • z‖ ≤ B := by rw [ha, hz]; exact hg θ w t hθ
              have h2 : |a - b| ≤ 2 * ‖θ - θ'‖ := by rw [ha, hb]; exact hδL _ _ _ _
              have h3 : ‖z‖ ≤ 1 / (1 - q) := by rw [hz]; exact htr w t
              rw [← ha, ← hb, ← hz]
              have e : inner ℝ (a • z - X θ) (θ - θstar) - inner ℝ (b • z - X θ') (θ' - θstar)
                  = inner ℝ (a • z - X θ) (θ - θ') + inner ℝ ((a - b) • z - (X θ - X θ')) (θ' - θstar) := by
                simp only [inner_sub_left, inner_sub_right, sub_smul]
                ring
              have hn := norm_nonneg (θ - θ')
              have h4 : inner ℝ (a • z - X θ) (θ - θ') ≤ 2 * B * ‖θ - θ'‖ := by
                refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ hn)
                refine (norm_sub_le _ _).trans ?_
                have := hXB θ hθ
                linarith
              have h5 : ‖(a - b) • z - (X θ - X θ')‖ ≤ 4 * ‖θ - θ'‖ / (1 - q) := by
                refine (norm_sub_le _ _).trans ?_
                have h6 : ‖(a - b) • z‖ ≤ 2 * ‖θ - θ'‖ * (1 / (1 - q)) := by
                  rw [norm_smul, Real.norm_eq_abs]
                  exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
                have h7 := hXL θ θ'
                have e7 : 4 * ‖θ - θ'‖ / (1 - q) = 2 * ‖θ - θ'‖ * (1 / (1 - q)) + 2 * ‖θ - θ'‖ / (1 - q) := by
                  ring
                linarith
              have h8 : inner ℝ ((a - b) • z - (X θ - X θ')) (θ' - θstar) ≤ 4 * B * ‖θ - θ'‖ := by
                refine (real_inner_le_norm _ _).trans ?_
                have h9 : ‖θ' - θstar‖ ≤ M := (hdiff θ' hθ').trans hRM
                calc _ ≤ (4 * ‖θ - θ'‖ / (1 - q)) * M := by
                      exact mul_le_mul h5 h9 (norm_nonneg _) (by positivity)
                  _ = 4 * B * ‖θ - θ'‖ := by rw [hB]; ring
              linarith [e, h4, h8]
            -- decomposition of Z
            have hZd : ∀ θ w t, Z θ w t = (∑ k ∈ Finset.range (t + 1), q ^ k *
                (inner ℝ (φ (w (t - k))) (θ - θstar) * tdErr γ Rw φ θ (w t) (w (t + 1))))
                - inner ℝ (X θ) (θ - θstar) := by
              intro θ w t
              rw [hZe, inner_sub_left, real_inner_smul_left, traceN, sum_inner, Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              rw [real_inner_smul_left]
              ring
            -- expectation of a single trace term
            have hterm : ∀ (ϑ : (ℕ → S) → EuclideanSpace ℝ (Fin d)) (a j k : ℕ),
                (∀ w w', (∀ i ≤ a, w i = w' i) → ϑ w = ϑ w') →
                E (a + j + k + 1) (fun w => inner ℝ (φ (w (a + j))) (ϑ w - θstar) *
                  tdErr γ Rw φ (ϑ w) (w (a + j + k)) (w (a + j + k + 1)))
                = E a (fun w => ∑ y, Q j (w a) y * D k (ϑ w) y) := by
              intro ϑ a j k hϑ
              rw [hstep (a + j + k) (fun w x => inner ℝ (φ (w (a + j))) (ϑ w - θstar) *
                  tdErr γ Rw φ (ϑ w) (w (a + j + k)) x)
                (fun w w' h => by
                  ext x
                  rw [hϑ w w' (fun i hi => h i (by omega)), h (a + j) (by omega), h (a + j + k) le_rfl])]
              have e1 : (fun w : ℕ → S => ∑ x, P (w (a + j + k)) x * (inner ℝ (φ (w (a + j))) (ϑ w - θstar) *
                  tdErr γ Rw φ (ϑ w) (w (a + j + k)) x)) =
                  fun w => (fun (w : ℕ → S) x => inner ℝ (φ (w (a + j))) (ϑ w - θstar) * u (ϑ w) x) w
                    (w (a + j + k)) := by
                funext w
                simp only
                rw [hutd, Finset.mul_sum]
                exact Finset.sum_congr rfl fun x _ => by ring
              rw [e1, hmulti k (a + j) (fun (w : ℕ → S) x => inner ℝ (φ (w (a + j))) (ϑ w - θstar) * u (ϑ w) x)
                (fun w w' h => by
                  ext x
                  rw [hϑ w w' (fun i hi => h i (by omega)), h (a + j) (by omega)])]
              have e2 : (fun w : ℕ → S => ∑ x, Q k (w (a + j)) x *
                  (inner ℝ (φ (w (a + j))) (ϑ w - θstar) * u (ϑ w) x)) =
                  fun w => (fun (w : ℕ → S) y => D k (ϑ w) y) w (w (a + j)) := by
                funext w
                simp only
                rw [hD, Finset.mul_sum]
                exact Finset.sum_congr rfl fun x _ => by ring
              rw [e2, hmulti j a (fun (w : ℕ → S) y => D k (ϑ w) y)
                (fun w w' h => by
                  ext x
                  rw [hϑ w w' h])]
            have hA0 : 0 ≤ M * M := mul_nonneg hM0 hM0
            have hAB : M * M / (1 - q) ≤ B ^ 2 := by
              have : M * M / (1 - q) = M * B := by rw [hB]; ring
              rw [this, sq]; exact mul_le_mul_of_nonneg_right hMB hB0
            -- core bound
            have hcore : ∀ (ϑ : (ℕ → S) → EuclideanSpace ℝ (Fin d)) (a t N : ℕ) (ε : ℝ), 0 ≤ ε →
                (∀ w, ‖ϑ w‖ ≤ R) → (∀ w w', (∀ i ≤ a, w i = w' i) → ϑ w = ϑ w') →
                a ≤ t → N ≤ t + 1 → a + N ≤ t + 1 →
                (∀ k < N, |E a (fun w => ∑ y, Q (t - k - a) (w a) y * D k (ϑ w) y)
                  - E a (fun w => ∑ y, π y * D k (ϑ w) y)| ≤ ε) →
                E (t + 1) (fun w => Z (ϑ w) w t) ≤ ε / (1 - q) + M * M * (q ^ N - q ^ (t + 1)) / (1 - q)
                  + M * M * q ^ N / (1 - q) := by
              intro ϑ a t N ε hε hϑR hϑ hat hN haN hk
              obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ k, b k = E (t + 1) (fun w =>
                inner ℝ (φ (w (t - k))) (ϑ w - θstar) * tdErr γ Rw φ (ϑ w) (w t) (w (t + 1))) :=
                ⟨_, fun _ => rfl⟩
              obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℝ, ∀ k, μ k = E a (fun w => ∑ y, π y * D k (ϑ w) y) :=
                ⟨_, fun _ => rfl⟩
              have h1 : E (t + 1) (fun w => Z (ϑ w) w t) = ∑ k ∈ Finset.range (t + 1), q ^ k * b k
                  - E (t + 1) (fun w => inner ℝ (X (ϑ w)) (ϑ w - θstar)) := by
                simp_rw [hZd]
                rw [hEsub, hEsum (t + 1) (t + 1) (fun k => q ^ k) (fun k w =>
                  inner ℝ (φ (w (t - k))) (ϑ w - θstar) * tdErr γ Rw φ (ϑ w) (w t) (w (t + 1)))]
                simp_rw [hb]
              have h2 : E (t + 1) (fun w => inner ℝ (X (ϑ w)) (ϑ w - θstar))
                  = E a (fun w => inner ℝ (X (ϑ w)) (ϑ w - θstar)) := by
                have := hmarg (t + 1 - a) a (fun w => inner ℝ (X (ϑ w)) (ϑ w - θstar))
                  (fun w w' h => by rw [hϑ w w' h])
                rw [← this]
                congr 1
                omega
              have h3 : ∀ k < N, b k ≤ μ k + ε := by
                intro k hkN
                have := (abs_le.1 (hk k hkN)).2
                rw [← hμ] at this
                have h4 := hterm ϑ a (t - k - a) k hϑ
                have e1 : a + (t - k - a) = t - k := by omega
                have e2 : t - k + k = t := by omega
                rw [e1, e2, ← hb] at h4
                linarith
              have h5 : ∀ k, b k ≤ M * M := by
                intro k
                rw [hb]
                refine le_trans (le_abs_self _) (hEabs _ _ _ fun w => ?_)
                rw [abs_mul]
                exact mul_le_mul ((hinn _ _).trans ((hdiff _ (hϑR w)).trans hRM)) (hδ _ _ _ (hϑR w))
                  (abs_nonneg _) hM0
              have h6 : ∑ k ∈ Finset.range N, q ^ k * μ k - E a (fun w => inner ℝ (X (ϑ w)) (ϑ w - θstar))
                  ≤ M * M * q ^ N / (1 - q) := by
                simp_rw [hμ]
                rw [← hEsum a N (fun k => q ^ k) (fun k w => ∑ y, π y * D k (ϑ w) y), ← hEsub]
                refine le_trans (le_abs_self _) (hEabs _ _ _ fun w => ?_)
                exact htrunc (ϑ w) N (hϑR w)
              have h7 : ∑ k ∈ Finset.range (t + 1), q ^ k * b k = ∑ k ∈ Finset.range N, q ^ k * b k
                  + ∑ k ∈ Finset.Ico N (t + 1), q ^ k * b k :=
                (Finset.sum_range_add_sum_Ico _ hN).symm
              have h8 : ∑ k ∈ Finset.Ico N (t + 1), q ^ k * b k ≤ M * M * (q ^ N - q ^ (t + 1)) / (1 - q) := by
                calc _ ≤ ∑ k ∈ Finset.Ico N (t + 1), q ^ k * (M * M) :=
                      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h5 k) (pow_nonneg hq0 k)
                  _ = _ := by
                    rw [← Finset.sum_mul, geom_sum_Ico' (ne_of_lt hq1) hN]
                    ring
              have h9 : ∑ k ∈ Finset.range N, q ^ k * b k ≤ ∑ k ∈ Finset.range N, q ^ k * μ k + ε / (1 - q) := by
                calc _ ≤ ∑ k ∈ Finset.range N, q ^ k * (μ k + ε) :=
                      Finset.sum_le_sum fun k hk' => mul_le_mul_of_nonneg_left
                        (h3 k (Finset.mem_range.1 hk')) (pow_nonneg hq0 k)
                  _ = ∑ k ∈ Finset.range N, q ^ k * μ k + (∑ k ∈ Finset.range N, q ^ k) * ε := by
                    simp_rw [mul_add]
                    rw [Finset.sum_add_distrib, Finset.sum_mul]
                  _ ≤ _ := by
                    have := mul_le_mul_of_nonneg_right (hgeo N) hε
                    have e : ε / (1 - q) = 1 / (1 - q) * ε := by ring
                    linarith
              rw [h1, h2, h7]
              linarith
            -- the projected iterates
            have hproj : ∀ x y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ R → ‖projBall R x - y‖ ≤ ‖x - y‖ := by
              intro x y hy
              unfold projBall
              split_ifs with h
              · exact le_rfl
              · rw [not_le] at h
                have hx : 0 < ‖x‖ := lt_of_le_of_lt hR0 h
                obtain ⟨c, hc⟩ : ∃ c, c = R / ‖x‖ := ⟨_, rfl⟩
                have hc0 : 0 ≤ c := by rw [hc]; positivity
                have hc1 : c ≤ 1 := by rw [hc, div_le_one hx]; exact h.le
                have hcx : c * ‖x‖ = R := by rw [hc]; field_simp
                rw [← hc]
                apply le_of_sq_le_sq _ (norm_nonneg _)
                rw [@norm_sub_sq_real, @norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
                  abs_of_nonneg hc0]
                have h1 : inner ℝ x y ≤ c * ‖x‖ ^ 2 := by
                  calc inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
                    _ ≤ ‖x‖ * R := mul_le_mul_of_nonneg_left hy hx.le
                    _ = c * ‖x‖ ^ 2 := by rw [← hcx]; ring
                have h2 : 0 ≤ (1 - c) * (c * ‖x‖ ^ 2 - inner ℝ x y) :=
                  mul_nonneg (by linarith) (by linarith)
                have h3 : 0 ≤ (1 - c) ^ 2 * ‖x‖ ^ 2 := by positivity
                linarith [h2, h3]
            have hprojR : ∀ x : EuclideanSpace ℝ (Fin d), ‖projBall R x‖ ≤ R := by
              intro x
              have := hproj x 0 (by simpa using hR0)
              unfold projBall at this ⊢
              split_ifs with h
              · exact h
              · rw [not_le] at h
                have hx : 0 < ‖x‖ := lt_of_le_of_lt hR0 h
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                apply le_of_eq
                field_simp
            have hth : ∀ (α : ℕ → ℝ) w t, ‖ptdLam γ lam Rw φ R α θ0 w t‖ ≤ R := by
              intro α w t
              cases t with
              | zero => exact hθ0
              | succ t => exact hprojR _
            have had : ∀ (α : ℕ → ℝ) t w w', (∀ i ≤ t, w i = w' i) →
                ptdLam γ lam Rw φ R α θ0 w t = ptdLam γ lam Rw φ R α θ0 w' t := by
              intro α t
              induction t with
              | zero => intro w w' _; rfl
              | succ t ih =>
                intro w w' h
                have h1 := ih w w' (fun i hi => h i (by omega))
                have h2 : traceN φ (γ * lam) w t = traceN φ (γ * lam) w' t := by
                  unfold traceN
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [h (t - k) (by omega)]
                simp only [ptdLam]
                rw [h1, h2, h t (by omega), h (t + 1) le_rfl]
            have hmove : ∀ (α : ℕ → ℝ) w a n, (∀ i < a + n, 0 ≤ α i) →
                ‖ptdLam γ lam Rw φ R α θ0 w (a + n) - ptdLam γ lam Rw φ R α θ0 w a‖
                  ≤ B * ∑ i ∈ Finset.range n, α (a + i) := by
              intro α w a n
              induction n with
              | zero => intro _; simp
              | succ n ih =>
                intro h
                have h1 := ih (fun i hi => h i (by omega))
                have h2 : ‖ptdLam γ lam Rw φ R α θ0 w (a + n + 1) - ptdLam γ lam Rw φ R α θ0 w (a + n)‖
                    ≤ α (a + n) * B := by
                  have e : ptdLam γ lam Rw φ R α θ0 w (a + n + 1) = projBall R (ptdLam γ lam Rw φ R α θ0 w (a + n) +
                    α (a + n) • (tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w (a + n)) (w (a + n)) (w (a + n + 1))
                      • traceN φ (γ * lam) w (a + n))) := rfl
                  rw [e]
                  refine (hproj _ _ (hth α w (a + n))).trans ?_
                  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (h _ (by omega)), ← hq]
                  exact mul_le_mul_of_nonneg_left (hg _ _ _ (hth _ _ _)) (h _ (by omega))
                rw [Finset.sum_range_succ]
                have h3 := norm_sub_le_norm_sub_add_norm_sub (ptdLam γ lam Rw φ R α θ0 w (a + n + 1))
                  (ptdLam γ lam Rw φ R α θ0 w (a + n)) (ptdLam γ lam Rw φ R α θ0 w a)
                have e : a + (n + 1) = a + n + 1 := rfl
                rw [e]
                linarith
            -- shift to an earlier iterate
            have hshift : ∀ (α : ℕ → ℝ) a n, (∀ i < a + n, 0 ≤ α i) →
                E (a + n + 1) (fun w => Z (ptdLam γ lam Rw φ R α θ0 w (a + n)) w (a + n)) ≤
                E (a + n + 1) (fun w => Z (ptdLam γ lam Rw φ R α θ0 w a) w (a + n))
                  + 6 * B ^ 2 * ∑ i ∈ Finset.range n, α (a + i) := by
              intro α a n h
              rw [← hEconst (a + n + 1) (6 * B ^ 2 * ∑ i ∈ Finset.range n, α (a + i)), ← hEadd]
              apply hEmono
              intro w
              refine (hLip _ (ptdLam γ lam Rw φ R α θ0 w a) w (a + n) (hth _ _ _) (hth _ _ _)).trans ?_
              have h1 := mul_le_mul_of_nonneg_left (hmove α w a n h) (by positivity : 0 ≤ 6 * B)
              linarith
            -- part (c), with step sizes nonnegative before t
            have hc : ∀ (α : ℕ → ℝ) t, (∀ i < t, 0 ≤ α i) →
                E (t + 1) (fun w => Z (ptdLam γ lam Rw φ R α θ0 w t) w t) ≤
                  6 * B ^ 2 * ∑ i ∈ Finset.range t, α i + B ^ 2 * q ^ t := by
              intro α t h
              have h1 := hshift α 0 t (by simpa using h)
              simp only [zero_add] at h1
              have h2 := hcore (fun w => ptdLam γ lam Rw φ R α θ0 w 0) 0 t (t + 1) 0 le_rfl
                (fun w => hth α w 0) (fun w w' h => had α 0 w w' h) (Nat.zero_le _) le_rfl (by omega)
                (by
                  intro k hk
                  have e : ∀ w, ptdLam γ lam Rw φ R α θ0 w 0 = θ0 := fun w => rfl
                  simp only [e]
                  rw [hEconst 0, hE0 (fun s => ∑ y, Q (t - k - 0) s y * D k θ0 y)]
                  simp_rw [Finset.mul_sum, ← mul_assoc]
                  rw [Finset.sum_comm]
                  simp_rw [← Finset.sum_mul, hπQ]
                  simp)
              rw [zero_div, sub_self, mul_zero, zero_div, zero_add, zero_add] at h2
              have h3 : M * M * q ^ (t + 1) / (1 - q) ≤ B ^ 2 * q ^ t := by
                have e : M * M * q ^ (t + 1) / (1 - q) = (M * M / (1 - q)) * q ^ t * q := by
                  rw [pow_succ]; ring
                rw [e]
                have h4 : (M * M / (1 - q)) * q ^ t ≤ B ^ 2 * q ^ t :=
                  mul_le_mul_of_nonneg_right hAB (pow_nonneg hq0 t)
                have h5 : 0 ≤ (M * M / (1 - q)) * q ^ t := by positivity
                exact (mul_le_of_le_one_right h5 hq1.le).trans h4
              linarith
            -- translate the goal
            have hgoal : ∀ (α : ℕ → ℝ) t, pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
                (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
                (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
                = E (t + 1) (fun w => Z (ptdLam γ lam Rw φ R α θ0 w t) w t) := by
              intro α t
              rw [hE, pathExp]
              simp_rw [hZ, hq]
            simp_rw [hgoal]
            rw [← hq, ← hM, ← hB]
            refine ⟨fun T α hα hαT => ⟨fun t ht htT => ?_, fun t ht htT => ?_⟩, fun α hα t => hc α t (fun i _ => hα i)⟩
            · obtain ⟨τ, hτ⟩ : ∃ τ, τ = tauMixLam m ρ q (α T) := ⟨_, rfl⟩
              rw [← hτ] at ht ⊢
              obtain ⟨hm, hρ0, hρ1, hmix⟩ := hA1
              have hτ1 : m * ρ ^ τ ≤ α T := by
                have hS : {t : ℕ | m * ρ ^ t ≤ α T}.Nonempty := by
                  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hαT hm) hρ1
                  refine ⟨n, ?_⟩
                  rw [lt_div_iff₀ hm] at hn
                  show m * ρ ^ n ≤ α T
                  linarith
                have h1 : m * ρ ^ (tauMix m ρ (α T)) ≤ α T := Nat.sInf_mem hS
                have h2 : tauMix m ρ (α T) ≤ τ := by rw [hτ]; exact le_max_left _ _
                have h3 : ρ ^ τ ≤ ρ ^ (tauMix m ρ (α T)) := pow_le_pow_of_le_one hρ0.le hρ1.le h2
                exact (mul_le_mul_of_nonneg_left h3 hm.le).trans h1
              have hτ2 : q ^ τ ≤ α T := by
                have hS : {t : ℕ | q ^ t ≤ α T}.Nonempty := by
                  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hαT hq1
                  exact ⟨n, hn.le⟩
                have h1 : q ^ (tauAlgo q (α T)) ≤ α T := Nat.sInf_mem hS
                have h2 : tauAlgo q (α T) ≤ τ := by rw [hτ]; exact le_max_right _ _
                exact (pow_le_pow_of_le_one hq0 hq1.le h2).trans h1
              obtain ⟨a, ha⟩ : ∃ a, t = a + 2 * τ := ⟨t - 2 * τ, by omega⟩
              have ha' : t - 2 * τ = a := by omega
              rw [ha']
              have hpos : ∀ i ≤ T, 0 ≤ α i := fun i hi => hαT.le.trans (hα i T hi le_rfl)
              have h1 := hshift α a (2 * τ) (fun i hi => hpos i (by omega))
              rw [← ha] at h1
              have h2 := hcore (fun w => ptdLam γ lam Rw φ R α θ0 w a) a t τ (2 * α T * (M * M))
                (by positivity)
                (fun w => hth α w a) (fun w w' h => had α a w w' h) (by omega) (by omega) (by omega)
                (by
                  intro k hk
                  rw [← hEsub]
                  apply hEabs
                  intro w
                  rw [← Finset.sum_sub_distrib]
                  have h3 := hmix (t - k - a) (w a)
                  unfold tvDist at h3
                  simp only [← hQ] at h3
                  have h4 : ρ ^ (t - k - a) ≤ ρ ^ τ := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
                  have h5 : ∑ s, |Q (t - k - a) (w a) s - π s| ≤ 2 * α T := by
                    have h6 := mul_le_mul_of_nonneg_left h4 hm.le
                    linarith
                  calc _ ≤ ∑ y, |Q (t - k - a) (w a) y * D k (ptdLam γ lam Rw φ R α θ0 w a) y
                          - π y * D k (ptdLam γ lam Rw φ R α θ0 w a) y| := Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ y, |Q (t - k - a) (w a) y - π y| * (M * M) := by
                      apply Finset.sum_le_sum
                      intro y _
                      rw [← sub_mul, abs_mul]
                      exact mul_le_mul_of_nonneg_left (hDb k _ y (hth α w a)) (abs_nonneg _)
                    _ = (∑ y, |Q (t - k - a) (w a) y - π y|) * (M * M) := by rw [Finset.sum_mul]
                    _ ≤ _ := mul_le_mul_of_nonneg_right h5 hA0)
              have h6 : ∑ i ∈ Finset.range (2 * τ), α (a + i) ≤ 2 * τ * α a := by
                calc _ ≤ ∑ i ∈ Finset.range (2 * τ), α a := by
                      apply Finset.sum_le_sum
                      intro i hi
                      rw [Finset.mem_range] at hi
                      exact hα a (a + i) (by omega) (by omega)
                  _ = _ := by simp
              have h7 : α T ≤ α a := hα a T (by omega) le_rfl
              have h8 : 0 ≤ q ^ (t + 1) := pow_nonneg hq0 _
              have h9 : 2 * α T * (M * M) / (1 - q) + M * M * (q ^ τ - q ^ (t + 1)) / (1 - q)
                  + M * M * q ^ τ / (1 - q) ≤ 4 * B ^ 2 * α a := by
                have e : 2 * α T * (M * M) / (1 - q) + M * M * (q ^ τ - q ^ (t + 1)) / (1 - q)
                  + M * M * q ^ τ / (1 - q) = (M * M / (1 - q)) * (2 * α T + 2 * q ^ τ - q ^ (t + 1)) := by ring
                rw [e]
                have h10 : 0 ≤ M * M / (1 - q) := by positivity
                calc _ ≤ (M * M / (1 - q)) * (4 * α a) := mul_le_mul_of_nonneg_left (by linarith) h10
                  _ ≤ B ^ 2 * (4 * α a) := mul_le_mul_of_nonneg_right hAB (by linarith)
                  _ = _ := by ring
              have h11 := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 6 * B ^ 2)
              have h12 : 0 ≤ B ^ 2 * α a := mul_nonneg (by positivity) (by linarith)
              linarith [h1, h2, h9, h11, h12]
            · obtain ⟨τ, hτ⟩ : ∃ τ, τ = tauMixLam m ρ q (α T) := ⟨_, rfl⟩
              rw [← hτ] at ht ⊢
              have hpos : ∀ i ≤ T, 0 ≤ α i := fun i hi => hαT.le.trans (hα i T hi le_rfl)
              have h1 := hc α t (fun i hi => hpos i (by omega))
              have h2 : ∑ i ∈ Finset.range t, α i ≤ t * α 0 := by
                calc _ ≤ ∑ i ∈ Finset.range t, α 0 := by
                      apply Finset.sum_le_sum
                      intro i hi
                      rw [Finset.mem_range] at hi
                      exact hα 0 i (by omega) (by omega)
                  _ = _ := by simp
              have h0 : 0 ≤ α 0 := hpos 0 (by omega)
              have h3 : (t : ℝ) ≤ 2 * τ := by exact_mod_cast ht
              have h4 : ∑ i ∈ Finset.range t, α i ≤ (1 + 2 * τ) * α 0 := by
                have h6 := mul_le_mul_of_nonneg_right h3 h0
                linarith
              have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 6 * B ^ 2)
              linarith
