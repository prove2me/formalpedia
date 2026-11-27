-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:04.351827+00:00
-- url     : https://prove2.me/submissions/2e3b9253-89ad-4c6a-8cb8-71fe970a1e81

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hR : ‖θstar‖ ≤ R) :
    -- (a), (b): any window l ≤ t of a two-sided path
    (∀ (w : ℤ → S) (l t : ℤ), l ≤ t → ∀ θ θ' : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ‖θ'‖ ≤ R →
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))|
          ≤ 2 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 ∧
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ' (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))|
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) * ‖θ - θ'‖) ∧
    -- (c): truncation of the trace
    (∀ (w : ℤ → S) (t : ℕ) (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R →
      (∀ τ : ℕ, τ ≤ t →
        |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w 0 t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w ((t : ℤ) - τ) t) (w t) (w (t + 1))|
          ≤ ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ τ) ∧
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w 0 t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ (traceInf φ (γ * lam) w t) (w t) (w (t + 1))|
          ≤ ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t) := by
            classical
            rcases isEmpty_or_nonempty S with hS | hS
            · refine ⟨fun w => ?_, fun w => ?_⟩ <;> exact isEmptyElim (w 0)
            have hrmax : 0 ≤ rmax := (abs_nonneg _).trans (hRw hS.some hS.some)
            have hq0 : 0 ≤ γ * lam := mul_nonneg hγ0 hlam0
            have hq1 : γ * lam < 1 := by
              calc γ * lam ≤ γ * 1 := mul_le_mul_of_nonneg_left hlam1 hγ0
                _ = γ := mul_one γ
                _ < 1 := hγ1
            have hc : 0 < 1 - γ * lam := by linarith
            have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
            set K : ℝ := 1 / (1 - γ * lam) with hK
            have hK0 : 0 < K := by positivity
            have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hc]; linarith
            have hBK : (rmax + 2 * R) / (1 - γ * lam) = (rmax + 2 * R) * K := by
              rw [hK, mul_one_div]
            rw [hBK]
            set B : ℝ := (rmax + 2 * R) * K with hB
            have hB0 : 0 ≤ B := by positivity
            have hB2R : 2 * R * K ≤ B := by rw [hB]; nlinarith
            have hB2R' : 2 * R ≤ B := by nlinarith
            -- inner product bound
            have hin : ∀ s (v : EuclideanSpace ℝ (Fin d)), |(inner ℝ (φ s) (v))| ≤ ‖v‖ := by
              intro s v
              refine (abs_real_inner_le_norm _ _).trans ?_
              nlinarith [hφ s, norm_nonneg (φ s), norm_nonneg v]
            -- TD error bounds
            have hδ : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ∀ s s',
                |tdErr γ Rw φ θ s s'| ≤ rmax + 2 * R := by
              intro θ hθ s s'
              have a1 := (hin s' θ).trans hθ
              have a2 := (hin s θ).trans hθ
              have a3 := hRw s s'
              unfold tdErr
              rw [abs_le] at a1 a2 a3 ⊢
              constructor <;> nlinarith
            have hδd : ∀ θ θ' : EuclideanSpace ℝ (Fin d), ∀ s s',
                |tdErr γ Rw φ θ s s' - tdErr γ Rw φ θ' s s'| ≤ 2 * ‖θ - θ'‖ := by
              intro θ θ' s s'
              have e : tdErr γ Rw φ θ s s' - tdErr γ Rw φ θ' s s'
                  = γ * (inner ℝ (φ s') (θ - θ')) - (inner ℝ (φ s) (θ - θ')) := by
                simp only [tdErr, inner_sub_right]; ring
              rw [e]
              have a1 := hin s' (θ - θ')
              have a2 := hin s (θ - θ')
              rw [abs_le] at a1 a2 ⊢
              constructor <;> nlinarith
            -- stochastic averaging
            have hP1 : ∀ s (x : S → ℝ) (M : ℝ), (∀ s', |x s'| ≤ M) → |∑ s', P s s' * x s'| ≤ M := by
              intro s x M h
              calc |∑ s', P s s' * x s'| ≤ ∑ s', |P s s' * x s'| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ s', P s s' * M := by
                    apply Finset.sum_le_sum
                    intro s' _
                    rw [abs_mul, abs_of_nonneg (hP.1 s s')]
                    exact mul_le_mul_of_nonneg_left (h s') (hP.1 s s')
                _ = M := by rw [← Finset.sum_mul, hP.2 s, one_mul]
            have hPk : ∀ (u : S → ℝ) (M : ℝ), (∀ s, |u s| ≤ M) → ∀ (k : ℕ) s,
                |(Matrix.mulVec (Matrix.of P ^ k) u) s| ≤ M := by
              intro u M hu k
              induction k with
              | zero => intro s; simpa using hu s
              | succ k ih =>
                intro s
                rw [pow_succ', ← Matrix.mulVec_mulVec]
                simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
                exact hP1 s _ M ih
            have hT : ∀ (u : S → ℝ) (M : ℝ), (∀ s, |u s| ≤ M) → ∀ s,
                Summable (fun k : ℕ => (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s) ∧
                |∑' k : ℕ, (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s| ≤ M * K := by
              intro u M hu s
              have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left M
              have bd : ∀ k : ℕ, ‖(γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s‖ ≤ M * (γ * lam) ^ k := by
                intro k
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 k), mul_comm M]
                exact mul_le_mul_of_nonneg_left (hPk u M hu k s) (pow_nonneg hq0 k)
              refine ⟨Summable.of_norm_bounded hg.summable bd, ?_⟩
              have := tsum_of_norm_bounded hg bd
              rw [Real.norm_eq_abs] at this
              rw [hK, mul_one_div]
              rwa [div_eq_mul_inv]
            have hSum : ∀ (u : S → ℝ) s,
                Summable (fun k : ℕ => (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s) := by
              intro u s
              exact (hT u (∑ t, |u t|) (fun s => Finset.single_le_sum (f := fun t => |u t|)
                (fun t _ => abs_nonneg _) (Finset.mem_univ s)) s).1
            have hTd : ∀ (u v : S → ℝ) (M : ℝ), (∀ s, |u s - v s| ≤ M) → ∀ s,
                |∑' k : ℕ, (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s
                  - ∑' k : ℕ, (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) v) s| ≤ M * K := by
              intro u v M h s
              rw [← (hSum u s).tsum_sub (hSum v s)]
              rw [tsum_congr (fun k => (by rw [Matrix.mulVec_sub, Pi.sub_apply, mul_sub] :
                (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) u) s - (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) v) s
                  = (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k) (u - v)) s))]
              exact (hT (u - v) M (fun s => by simpa using h s) s).2
            have hX : ∀ θ : EuclideanSpace ℝ (Fin d), xbar π P γ lam Rw φ θ
                = ∑ s, (π s * ∑' k : ℕ, (γ * lam) ^ k * (Matrix.mulVec (Matrix.of P ^ k)
                    (fun u => ∑ u', P u u' * tdErr γ Rw φ θ u u')) s) • φ s := by
              intro θ
              unfold xbar gbarH Tlam
              simp only [add_sub_cancel_left]
              rfl
            have G : ∀ (c : S → ℝ) (C : ℝ), (∀ s, |c s| ≤ C) → ‖∑ s, (π s * c s) • φ s‖ ≤ C := by
              intro c C h
              calc ‖∑ s, (π s * c s) • φ s‖ ≤ ∑ s, ‖(π s * c s) • φ s‖ := norm_sum_le _ _
                _ ≤ ∑ s, π s * C := by
                    apply Finset.sum_le_sum
                    intro s _
                    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 s)]
                    have h2 : 0 ≤ π s * |c s| := mul_nonneg (hπ.1 s) (abs_nonneg _)
                    exact (mul_le_of_le_one_right h2 (hφ s)).trans
                      (mul_le_mul_of_nonneg_left (h s) (hπ.1 s))
                _ = C := by rw [← Finset.sum_mul, hπ.2.1, one_mul]
            have G' : ∀ (a b : S → ℝ) (C : ℝ), (∀ s, |a s - b s| ≤ C) →
                ‖∑ s, (π s * a s) • φ s - ∑ s, (π s * b s) • φ s‖ ≤ C := by
              intro a b C h
              have : ∑ s, (π s * a s) • φ s - ∑ s, (π s * b s) • φ s
                  = ∑ s, (π s * (a s - b s)) • φ s := by
                rw [← Finset.sum_sub_distrib]
                congr 1; funext s; rw [mul_sub, sub_smul]
              rw [this]; exact G _ C h
            have hxb : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ‖xbar π P γ lam Rw φ θ‖ ≤ B := by
              intro θ hθ
              rw [hX]
              apply G
              intro s
              exact (hT _ (rmax + 2 * R) (fun u => hP1 u _ _ (fun u' => hδ θ hθ u u')) s).2
            have hxd : ∀ θ θ' : EuclideanSpace ℝ (Fin d),
                ‖xbar π P γ lam Rw φ θ - xbar π P γ lam Rw φ θ'‖ ≤ 2 * ‖θ - θ'‖ * K := by
              intro θ θ'
              rw [hX, hX]
              apply G'
              intro s
              apply hTd
              intro u
              rw [← Finset.sum_sub_distrib]
              simp_rw [← mul_sub]
              exact hP1 u _ _ (fun u' => hδd θ θ' u u')
            -- trace bound
            have hz : ∀ (w : ℤ → S) (l t : ℤ), ‖traceWin φ (γ * lam) w l t‖ ≤ K := by
              intro w l t
              unfold traceWin
              calc ‖∑ k ∈ Finset.range ((t - l).toNat + 1), (γ * lam) ^ k • φ (w (t - k))‖
                  ≤ ∑ k ∈ Finset.range ((t - l).toNat + 1), ‖(γ * lam) ^ k • φ (w (t - k))‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ k ∈ Finset.range ((t - l).toNat + 1), (γ * lam) ^ k := by
                    apply Finset.sum_le_sum
                    intro k _
                    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 k)]
                    exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
                _ ≤ ∑' k : ℕ, (γ * lam) ^ k :=
                    (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
                _ = K := by rw [tsum_geometric_of_lt_one hq0 hq1, hK, one_div]
            -- zeta algebra
            have hζ1 : ∀ (θ z : EuclideanSpace ℝ (Fin d)) s s',
                zetaLam π P γ lam Rw φ θstar θ z s s'
                  = (inner ℝ (tdErr γ Rw φ θ s s' • z) (θ - θstar)) - (inner ℝ (xbar π P γ lam Rw φ θ) (θ - θstar)) := by
              intro θ z s s'
              simp only [zetaLam, inner_sub_left]
            have he : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ‖θ - θstar‖ ≤ 2 * R := by
              intro θ hθ
              exact (norm_sub_le _ _).trans (by linarith)
            have hn1 : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ∀ (w : ℤ → S) (l t : ℤ) s s',
                ‖tdErr γ Rw φ θ s s' • traceWin φ (γ * lam) w l t‖ ≤ B := by
              intro θ hθ w l t s s'
              rw [norm_smul, Real.norm_eq_abs, hB]
              exact mul_le_mul (hδ θ hθ s s') (hz w l t) (norm_nonneg _) (by linarith)
            have hζz : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ∀ (z z' : EuclideanSpace ℝ (Fin d)) s s'
                (m : ℕ), ‖z - z'‖ ≤ (γ * lam) ^ m * K →
                |zetaLam π P γ lam Rw φ θstar θ z s s' - zetaLam π P γ lam Rw φ θstar θ z' s s'|
                  ≤ B ^ 2 * (γ * lam) ^ m := by
              intro θ hθ z z' s s' m hzz
              have e : zetaLam π P γ lam Rw φ θstar θ z s s' - zetaLam π P γ lam Rw φ θstar θ z' s s'
                  = (inner ℝ (tdErr γ Rw φ θ s s' • (z - z')) (θ - θstar)) := by
                simp only [zetaLam, inner_sub_left, smul_sub]; ring
              rw [e]
              have hqm : 0 ≤ (γ * lam) ^ m := pow_nonneg hq0 m
              calc |(inner ℝ (tdErr γ Rw φ θ s s' • (z - z')) (θ - θstar))|
                  ≤ ‖tdErr γ Rw φ θ s s' • (z - z')‖ * ‖θ - θstar‖ := abs_real_inner_le_norm _ _
                _ ≤ ((rmax + 2 * R) * ((γ * lam) ^ m * K)) * (2 * R) := by
                    rw [norm_smul, Real.norm_eq_abs]
                    exact mul_le_mul (mul_le_mul (hδ θ hθ s s') hzz (norm_nonneg _) (by linarith))
                      (he θ hθ) (norm_nonneg _) (by positivity)
                _ ≤ ((rmax + 2 * R) * ((γ * lam) ^ m * K)) * B :=
                    mul_le_mul_of_nonneg_left hB2R' (by positivity)
                _ = B ^ 2 * (γ * lam) ^ m := by rw [hB]; ring
            refine ⟨?_, ?_⟩
            · intro w l t _ θ θ' hθ hθ'
              set z := traceWin φ (γ * lam) w l t with hzdef
              refine ⟨?_, ?_⟩
              · rw [hζ1]
                have i1 := abs_real_inner_le_norm (tdErr γ Rw φ θ (w t) (w (t + 1)) • z) (θ - θstar)
                have i2 := abs_real_inner_le_norm (xbar π P γ lam Rw φ θ) (θ - θstar)
                have n1 := hn1 θ hθ w l t (w t) (w (t + 1))
                have n2 := hxb θ hθ
                have e1 := he θ hθ
                calc _ ≤ |(inner ℝ (tdErr γ Rw φ θ (w t) (w (t + 1)) • z) (θ - θstar))|
                      + |(inner ℝ (xbar π P γ lam Rw φ θ) (θ - θstar))| := abs_sub _ _
                  _ ≤ B * (2 * R) + B * (2 * R) := add_le_add
                      (i1.trans (mul_le_mul n1 e1 (norm_nonneg _) hB0))
                      (i2.trans (mul_le_mul n2 e1 (norm_nonneg _) hB0))
                  _ ≤ 2 * B ^ 2 := by nlinarith
              · set δ := tdErr γ Rw φ θ (w t) (w (t + 1)) with hδdef
                set δ' := tdErr γ Rw φ θ' (w t) (w (t + 1)) with hδ'def
                set X := xbar π P γ lam Rw φ θ with hXdef
                set X' := xbar π P γ lam Rw φ θ' with hX'def
                have key : zetaLam π P γ lam Rw φ θstar θ z (w t) (w (t + 1))
                    - zetaLam π P γ lam Rw φ θstar θ' z (w t) (w (t + 1))
                    = (inner ℝ ((δ • z - X) - (δ' • z - X')) (θ - θstar)) + (inner ℝ (δ' • z - X') (θ - θ')) := by
                  simp only [zetaLam, inner_sub_left, inner_sub_right]
                  ring
                rw [key]
                have hA : ‖(δ • z - X) - (δ' • z - X')‖ ≤ 2 * ‖θ - θ'‖ * K + 2 * ‖θ - θ'‖ * K := by
                  have : (δ • z - X) - (δ' • z - X') = (δ - δ') • z - (X - X') := by
                    rw [sub_smul]; abel
                  rw [this]
                  refine (norm_sub_le _ _).trans (add_le_add ?_ (hxd θ θ'))
                  rw [norm_smul, Real.norm_eq_abs]
                  exact mul_le_mul (hδd θ θ' _ _) (hz w l t) (norm_nonneg _) (by positivity)
                have hA' : ‖δ' • z - X'‖ ≤ 2 * B := by
                  refine (norm_sub_le _ _).trans ?_
                  have := hn1 θ' hθ' w l t (w t) (w (t + 1))
                  have := hxb θ' hθ'
                  linarith
                have i1 := abs_real_inner_le_norm ((δ • z - X) - (δ' • z - X')) (θ - θstar)
                have i2 := abs_real_inner_le_norm (δ' • z - X') (θ - θ')
                have e1 := he θ hθ
                have hΔ := norm_nonneg (θ - θ')
                calc _ ≤ |(inner ℝ ((δ • z - X) - (δ' • z - X')) (θ - θstar))| + |(inner ℝ (δ' • z - X') (θ - θ'))| :=
                      abs_add_le _ _
                  _ ≤ (2 * ‖θ - θ'‖ * K + 2 * ‖θ - θ'‖ * K) * (2 * R) + 2 * B * ‖θ - θ'‖ := add_le_add
                      (i1.trans (mul_le_mul hA e1 (norm_nonneg _) (by positivity)))
                      (i2.trans (mul_le_mul_of_nonneg_right hA' hΔ))
                  _ ≤ 6 * B * ‖θ - θ'‖ := by
                      have := mul_le_mul_of_nonneg_right hB2R hΔ
                      nlinarith
            · intro w t θ hθ
              have hf : Summable (fun k : ℕ => (γ * lam) ^ k • φ (w ((t : ℤ) - k))) := by
                refine Summable.of_norm_bounded (summable_geometric_of_lt_one hq0 hq1) (fun k => ?_)
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 k)]
                exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
              refine ⟨?_, ?_⟩
              · intro τ hτ
                apply hζz θ hθ
                have h1 : ((t : ℤ) - 0).toNat = t := by simp
                have h2 : ((t : ℤ) - ((t : ℤ) - τ)).toNat = τ := by simp
                unfold traceWin
                rw [h1, h2, ← Finset.sum_Ico_eq_sub _ (by omega : τ + 1 ≤ t + 1)]
                calc _ ≤ ∑ k ∈ Finset.Ico (τ + 1) (t + 1), ‖(γ * lam) ^ k • φ (w ((t : ℤ) - k))‖ :=
                      norm_sum_le _ _
                  _ ≤ ∑ k ∈ Finset.Ico (τ + 1) (t + 1), (γ * lam) ^ k := by
                      apply Finset.sum_le_sum
                      intro k _
                      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 k)]
                      exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
                  _ ≤ (γ * lam) ^ (τ + 1) / (1 - γ * lam) := geom_sum_Ico_le_of_lt_one hq0 hq1
                  _ ≤ (γ * lam) ^ τ * K := by
                      rw [hK, mul_one_div]
                      apply div_le_div_of_nonneg_right _ hc.le
                      exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
              · apply hζz θ hθ
                unfold traceWin traceInf
                have h1 : ((t : ℤ) - 0).toNat = t := by simp
                rw [h1, ← hf.sum_add_tsum_nat_add (t + 1)]
                rw [sub_add_cancel_left, norm_neg]
                have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((γ * lam) ^ (t + 1))
                refine (tsum_of_norm_bounded hg (fun i => ?_)).trans ?_
                · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 _), pow_add, mul_comm]
                  calc ‖φ (w (↑t - ↑(i + (t + 1))))‖ * ((γ * lam) ^ i * (γ * lam) ^ (t + 1))
                      ≤ 1 * ((γ * lam) ^ i * (γ * lam) ^ (t + 1)) :=
                        mul_le_mul_of_nonneg_right (hφ _) (by positivity)
                    _ = (γ * lam) ^ (t + 1) * (γ * lam) ^ i := by ring
                · rw [hK, one_div]
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
