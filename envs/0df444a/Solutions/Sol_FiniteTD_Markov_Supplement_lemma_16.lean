-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:42.238403+00:00
-- url     : https://prove2.me/submissions/2a8d3f75-af2e-403b-a828-69072bb4b1a6

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar))) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - kappa γ lam) * dNormSq π φ (θstar - θ) ≤
        ⟪θstar - θ, xbar π P γ lam Rw φ θ⟫_ℝ := by
          intro θ
          classical
          set q : ℝ := γ * lam with hq
          set M : Matrix S S ℝ := Matrix.of P with hM
          have hq0 : 0 ≤ q := mul_nonneg hγ0 hlam0
          have hq1 : q < 1 := by
            have : γ * lam ≤ γ := mul_le_of_le_one_right hγ0 hlam1
            linarith
          have hinner : ∀ a b : EuclideanSpace ℝ (Fin d), ⟪a, b⟫_ℝ = ∑ i, a i * b i := by
            intro a b; simp [PiLp.inner_apply, mul_comm]
          have hMv : ∀ (g : S → ℝ) s, (Matrix.mulVec (M) (g)) s = ∑ u, P s u * g u := by
            intro g s; simp [hM, Matrix.mulVec, dotProduct]
          -- sup bound
          have hbd : ∀ (k : ℕ) (f : S → ℝ) (B : ℝ), (∀ u, |f u| ≤ B) → ∀ s, |(Matrix.mulVec (M ^ k) (f)) s| ≤ B := by
            intro k
            induction k with
            | zero => intro f B hf s; simpa using hf s
            | succ k ih =>
              intro f B hf s
              rw [pow_succ', ← Matrix.mulVec_mulVec, hMv]
              have h1 := ih f B hf
              calc |∑ u, P s u * (Matrix.mulVec (M ^ k) (f)) u| ≤ ∑ u, |P s u * (Matrix.mulVec (M ^ k) (f)) u| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ u, P s u * B := by
                  apply Finset.sum_le_sum; intro u _
                  rw [abs_mul, abs_of_nonneg (hP.1 s u)]
                  exact mul_le_mul_of_nonneg_left (h1 u) (hP.1 s u)
                _ = B := by rw [← Finset.sum_mul, hP.2 s, one_mul]
          have hsum : ∀ (f : S → ℝ) s, Summable (fun k : ℕ => q ^ k * (Matrix.mulVec (M ^ k) (f)) s) := by
            intro f s
            have hB : ∀ u, |f u| ≤ ∑ v, |f v| := fun u =>
              Finset.single_le_sum (f := fun v => |f v|) (fun v _ => abs_nonneg _) (Finset.mem_univ u)
            refine Summable.of_norm_bounded
              ((summable_geometric_of_lt_one hq0 hq1).mul_right (∑ v, |f v|)) ?_
            intro k
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 k)]
            exact mul_le_mul_of_nonneg_left (hbd k f _ hB s) (pow_nonneg hq0 k)
          have hsum1 : ∀ (f : S → ℝ) s, Summable (fun k : ℕ => q ^ k * (Matrix.mulVec (M ^ (k + 1)) (f)) s) := by
            intro f s
            refine (hsum (Matrix.mulVec (M) (f)) s).congr ?_
            intro k
            rw [Matrix.mulVec_mulVec, ← pow_succ]
          -- Jensen
          have hjen1 : ∀ g : S → ℝ, ∑ s, π s * ((Matrix.mulVec (M) (g)) s) ^ 2 ≤ ∑ s, π s * g s ^ 2 := by
            intro g
            have hpt : ∀ s, ((Matrix.mulVec (M) (g)) s) ^ 2 ≤ ∑ u, P s u * g u ^ 2 := by
              intro s
              rw [hMv]
              generalize hm : ∑ u, P s u * g u = m
              have h0 : 0 ≤ ∑ u, P s u * (g u - m) ^ 2 :=
                Finset.sum_nonneg (fun u _ => mul_nonneg (hP.1 s u) (sq_nonneg _))
              have h1 : ∑ u, P s u * (g u - m) ^ 2
                  = ∑ u, P s u * g u ^ 2 - 2 * m * (∑ u, P s u * g u) + m ^ 2 * ∑ u, P s u := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro u _; ring
              rw [h1, hP.2 s, hm] at h0
              nlinarith
            calc ∑ s, π s * ((Matrix.mulVec (M) (g)) s) ^ 2 ≤ ∑ s, π s * ∑ u, P s u * g u ^ 2 :=
                  Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hπ.1 s))
              _ = ∑ u, (∑ s, π s * P s u) * g u ^ 2 := by
                  simp_rw [Finset.mul_sum, Finset.sum_mul]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro s _; ring
              _ = ∑ u, π u * g u ^ 2 := by
                  apply Finset.sum_congr rfl; intro u _; rw [hπ.2.2 u]
          have hjen : ∀ (k : ℕ) (g : S → ℝ), ∑ s, π s * ((Matrix.mulVec (M ^ k) (g)) s) ^ 2 ≤ ∑ s, π s * g s ^ 2 := by
            intro k
            induction k with
            | zero => intro g; simp
            | succ k ih =>
              intro g
              rw [pow_succ', ← Matrix.mulVec_mulVec]
              exact (hjen1 _).trans (ih g)
          -- Tlam difference
          have hTdiff : ∀ (v v' : S → ℝ) s, Tlam P γ lam Rw v s - Tlam P γ lam Rw v' s
              = γ * (1 - lam) * ∑' k : ℕ, q ^ k * (Matrix.mulVec (M ^ (k + 1)) ((v - v'))) s := by
            intro v v' s
            set Δ := v - v' with hΔ
            set r : (S → ℝ) → S → ℝ := fun v u => ∑ u', P u u' * (Rw u u' + γ * v u' - v u) with hr
            have hrd : r v - r v' = γ • (Matrix.mulVec (M) (Δ)) - Δ := by
              funext u
              simp only [hr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hMv, hΔ]
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              have : v u - v' u = ∑ u', P u u' * (v u - v' u) := by
                rw [← Finset.sum_mul, hP.2 u, one_mul]
              rw [this, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro u' _; ring
            have hT : ∀ w, Tlam P γ lam Rw w s = w s + ∑' k : ℕ, q ^ k * (Matrix.mulVec (M ^ k) (r w)) s := by
              intro w; rfl
            rw [hT, hT, add_sub_add_comm, ← (hsum _ s).tsum_sub (hsum _ s)]
            have h2 : ∀ k : ℕ, q ^ k * (Matrix.mulVec (M ^ k) (r v)) s - q ^ k * (Matrix.mulVec (M ^ k) (r v')) s
                = γ * (q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s) - q ^ k * (Matrix.mulVec (M ^ k) (Δ)) s := by
              intro k
              rw [← mul_sub, ← Pi.sub_apply (Matrix.mulVec (M ^ k) (r v)), ← Matrix.mulVec_sub, hrd, Matrix.mulVec_sub,
                Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ]
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
            simp_rw [h2]
            rw [((hsum1 Δ s).mul_left γ).tsum_sub (hsum Δ s), tsum_mul_left,
              (hsum Δ s).tsum_eq_zero_add]
            have h3 : ∑' k : ℕ, q ^ (k + 1) * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s
                = q * ∑' k : ℕ, q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s := by
              rw [← tsum_mul_left]; congr 1; funext k; ring
            rw [h3]
            simp only [pow_zero, one_mul, Matrix.one_mulVec, hΔ, Pi.sub_apply, hq]
            ring
          -- gram invertible
          have hgram : IsUnit (gram π φ).det := by
            rw [isUnit_iff_ne_zero]
            intro hdet
            obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
            set x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v with hxdef
            have hx : dNormSq π φ x = 0 := by
              have h1 : dotProduct v (Matrix.mulVec (gram π φ) v) = 0 := by rw [hv, dotProduct_zero]
              have h2 : dotProduct v (Matrix.mulVec (gram π φ) v) = dNormSq π φ x := by
                simp only [dNormSq, dotProduct, Matrix.mulVec, gram, Matrix.of_apply, hinner, hxdef,
                  sq, Finset.mul_sum, Finset.sum_mul]
                calc _ = ∑ i, ∑ s, ∑ j, v i * (π s * φ s i * φ s j * v j) := by
                      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
                  _ = _ := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl; intro s _
                      apply Finset.sum_congr rfl; intro i _
                      apply Finset.sum_congr rfl; intro j _
                      ring
              linarith
            have hxn : ‖x‖ ≠ 0 := by
              rw [norm_ne_zero_iff]; intro h; apply hv0
              have := congrArg WithLp.ofLp h
              simpa [hxdef] using this
            have hu : ‖(‖x‖⁻¹) • x‖ = 1 := by
              rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
            have hle := hω.2 ⟨_, hu, rfl⟩
            have h0 : dNormSq π φ ((‖x‖⁻¹) • x) = 0 := by
              have : dNormSq π φ ((‖x‖⁻¹) • x) = (‖x‖⁻¹) ^ 2 * dNormSq π φ x := by
                simp only [dNormSq, inner_smul_right, Finset.mul_sum]
                apply Finset.sum_congr rfl; intro s _; ring
              rw [this, hx, mul_zero]
            rw [h0] at hle
            linarith
          have hgi : gram π φ * (gram π φ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgram
          set Vs := valFn φ θstar with hVs
          set Vt := valFn φ θ with hVt
          have horth : ∀ i, ∑ s, π s * (Tlam P γ lam Rw Vs s - Vs s) * φ s i = 0 := by
            intro i
            set w := Tlam P γ lam Rw Vs with hw
            set b : Fin d → ℝ := fun i => ∑ s, π s * w s * φ s i with hb
            set c := Matrix.mulVec (gram π φ)⁻¹ b with hc
            have hV : ∀ s, Vs s = ∑ j, φ s j * c j := by
              intro s
              rw [congrFun hfix s]
              show ⟪φ s, WithLp.toLp 2 (Matrix.mulVec ((gram π φ)⁻¹) (b))⟫_ℝ = _
              rw [hinner]
            have hgb : Matrix.mulVec (gram π φ) c = b := by rw [hc, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
            have := congrFun hgb i
            simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, hb] at this
            have e1 : ∑ s, π s * (w s - Vs s) * φ s i
                = ∑ s, π s * w s * φ s i - ∑ s, π s * Vs s * φ s i := by
              rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro s _; ring
            have e2 : ∑ s, π s * Vs s * φ s i = ∑ j, (∑ s, π s * φ s i * φ s j) * c j := by
              simp_rw [hV, Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro s _; ring
            rw [e1, e2, this, sub_self]
          set Δ : S → ℝ := Vt - Vs with hΔ
          set X : S → ℝ := fun s => ∑' k : ℕ, q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s with hX
          set N := ∑ s, π s * Δ s ^ 2 with hN
          have hNd : dNormSq π φ (θstar - θ) = N := by
            simp only [dNormSq, hN]
            apply Finset.sum_congr rfl; intro s _
            rw [inner_sub_right]
            simp only [hΔ, hVs, hVt, valFn, Pi.sub_apply]
            ring
          have hLHS : ⟪θstar - θ, xbar π P γ lam Rw φ θ⟫_ℝ
              = ∑ s, π s * (Tlam P γ lam Rw Vt s - Vt s) * (Vs s - Vt s) := by
            simp only [xbar, gbarH, inner_sum, inner_smul_right]
            apply Finset.sum_congr rfl; intro s _
            rw [real_inner_comm, inner_sub_right]
            simp only [hVs, hVt, valFn]
          have hfix0 : ∑ s, π s * (Tlam P γ lam Rw Vs s - Vs s) * (Vs s - Vt s) = 0 := by
            have hd : ∀ s, Vs s - Vt s = ∑ i, φ s i * (θstar - θ) i := by
              intro s; show ⟪φ s, θstar⟫_ℝ - ⟪φ s, θ⟫_ℝ = _; rw [← inner_sub_right, hinner]
            simp_rw [hd, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_eq_zero; intro i _
            calc ∑ s, π s * (Tlam P γ lam Rw Vs s - Vs s) * (φ s i * (θstar - θ) i)
                = (θstar - θ) i * ∑ s, π s * (Tlam P γ lam Rw Vs s - Vs s) * φ s i := by
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
              _ = 0 := by rw [horth i, mul_zero]
          have hcross : ∑ s, π s * Δ s * X s ≤ N / (1 - q) := by
            have hck : ∀ k : ℕ, ∑ s, π s * Δ s * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s ≤ N := by
              intro k
              have hj := hjen (k + 1) Δ
              have : ∑ s, π s * Δ s * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s
                  ≤ ∑ s, π s * ((Δ s ^ 2 + ((Matrix.mulVec (M ^ (k + 1)) (Δ)) s) ^ 2) / 2) := by
                apply Finset.sum_le_sum; intro s _
                have := two_mul_le_add_sq (Δ s) ((Matrix.mulVec (M ^ (k + 1)) (Δ)) s)
                have hp := hπ.1 s
                rw [mul_assoc]
                apply mul_le_mul_of_nonneg_left _ hp
                linarith
              have e : ∑ s, π s * ((Δ s ^ 2 + ((Matrix.mulVec (M ^ (k + 1)) (Δ)) s) ^ 2) / 2)
                  = (N + ∑ s, π s * ((Matrix.mulVec (M ^ (k + 1)) (Δ)) s) ^ 2) / 2 := by
                rw [hN, ← Finset.sum_add_distrib, Finset.sum_div]
                apply Finset.sum_congr rfl; intro s _; ring
              linarith
            calc ∑ s, π s * Δ s * X s
                = ∑ s, ∑' k : ℕ, π s * Δ s * (q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s) := by
                  apply Finset.sum_congr rfl; intro s _; rw [hX, tsum_mul_left]
              _ = ∑' k : ℕ, ∑ s, π s * Δ s * (q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s) :=
                  (Summable.tsum_finsetSum (fun s _ => (hsum1 Δ s).mul_left _)).symm
              _ ≤ ∑' k : ℕ, q ^ k * N := by
                  refine Summable.tsum_le_tsum (fun k => ?_)
                    (summable_sum (fun s _ => (hsum1 Δ s).mul_left _))
                    ((summable_geometric_of_lt_one hq0 hq1).mul_right N)
                  have : ∑ s, π s * Δ s * (q ^ k * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s)
                      = q ^ k * ∑ s, π s * Δ s * (Matrix.mulVec (M ^ (k + 1)) (Δ)) s := by
                    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
                  rw [this]
                  exact mul_le_mul_of_nonneg_left (hck k) (pow_nonneg hq0 k)
              _ = N / (1 - q) := by
                  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv, mul_comm]
          have hmain : ∑ s, π s * (Tlam P γ lam Rw Vt s - Vt s) * (Vs s - Vt s)
              = N - γ * (1 - lam) * ∑ s, π s * Δ s * X s := by
            rw [← sub_zero (∑ s, π s * (Tlam P γ lam Rw Vt s - Vt s) * (Vs s - Vt s)), ← hfix0,
              ← Finset.sum_sub_distrib, hN, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro s _
            have h := hTdiff Vt Vs s
            have hΔs : Δ s = Vt s - Vs s := rfl
            have hXs : X s = ∑' k : ℕ, q ^ k * (Matrix.mulVec (M ^ (k + 1)) ((Vt - Vs))) s := rfl
            rw [hΔs, hXs]
            linear_combination (π s * (Vs s - Vt s)) * h
          rw [hNd, hLHS, hmain]
          have hg : 0 ≤ γ * (1 - lam) := mul_nonneg hγ0 (by linarith)
          have := mul_le_mul_of_nonneg_left hcross hg
          have hk : (1 - kappa γ lam) * N = N - γ * (1 - lam) * (N / (1 - q)) := by
            simp only [kappa]; rw [← hq]; ring
          rw [hk]
          linarith
