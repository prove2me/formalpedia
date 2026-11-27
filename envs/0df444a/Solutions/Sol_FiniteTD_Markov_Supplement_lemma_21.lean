-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:29.497237+00:00
-- url     : https://prove2.me/submissions/544ebe14-b890-48cc-961e-f4f88f8aa042

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ)
    (H : (S → ℝ) → (S → ℝ)) (c : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ v v' : S → ℝ,
      dNormV π (projD π φ (H v) - projD π φ (H v')) ≤ c * dNormV π (v - v'))
    (hfix : valFn φ θstar = projD π φ (H (valFn φ θstar))) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - c) * dNormSq π φ (θstar - θ) ≤ ⟪θstar - θ, gbarH π φ H θ⟫_ℝ := by
        classical
        have hscale (a : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
            dNormSq π φ (a • x) = a ^ 2 * dNormSq π φ x := by
          simp only [dNormSq, inner_smul_right, Real.ringHom_apply, mul_pow,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        have hpos (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) :
            0 < dNormSq π φ x := by
          have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
            simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), hn]
          have hl : ω ≤ dNormSq π φ ((‖x‖⁻¹ : ℝ) • x) :=
            hω.2 ⟨_, hu, rfl⟩
          rw [hscale] at hl
          by_contra! hz
          have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (‖x‖⁻¹)) hz
          linarith
        have hact (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
            (Matrix.mulVec (gram π φ) (fun j => x j)) i =
              ∑ s, π s * valFn φ x s * φ s i := by
          simp only [gram, Matrix.mulVec, dotProduct, Matrix.of_apply, valFn,
            PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro j hj
          ring
        have hquad (x : EuclideanSpace ℝ (Fin d)) :
            dotProduct (fun i => x i) (Matrix.mulVec (gram π φ) (fun i => x i)) = dNormSq π φ x := by
          simp_rw [dotProduct, hact, Finset.mul_sum]
          rw [Finset.sum_comm]
          unfold dNormSq
          apply Finset.sum_congr rfl
          intro s hs
          simp only [valFn, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        have hunit : IsUnit (gram π φ) := by
          apply Matrix.mulVec_injective_iff_isUnit.mp
          intro x y hxy
          have hz : Matrix.mulVec (gram π φ) (x - y) = 0 := by
            rw [Matrix.mulVec_sub, hxy, sub_self]
          have hq := hquad (WithLp.toLp 2 (x - y))
          have : dNormSq π φ (WithLp.toLp 2 (x - y)) = 0 := by
            change dotProduct (x - y) (Matrix.mulVec (gram π φ) (x - y)) = _ at hq
            rw [← hq, hz]
            simp
          have he : WithLp.toLp 2 (x - y) = 0 := by
            by_contra hn
            have := hpos _ hn
            linarith
          have : x - y = 0 := by simpa using congrArg (WithLp.ofLp) he
          exact sub_eq_zero.mp this
        have hnormal (v : S → ℝ) (i : Fin d) :
            ∑ s, π s * projD π φ v s * φ s i = ∑ s, π s * v s * φ s i := by
          have hn : Matrix.mulVec (gram π φ) (fun j => projCoef π φ v j) =
              (fun j => ∑ s, π s * v s * φ s j) := by
            change Matrix.mulVec (gram π φ)
              (Matrix.mulVec (gram π φ)⁻¹ (fun j => ∑ s, π s * v s * φ s j)) = _
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
              ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mulVec]
          change (∑ s, π s * valFn φ (projCoef π φ v) s * φ s i) = _
          rw [← hact (projCoef π φ v) i]
          exact congrFun hn i
        have hpair (x : EuclideanSpace ℝ (Fin d)) (v : S → ℝ) :
            ∑ s, π s * valFn φ x s * v s =
              ∑ i, x i * (∑ s, π s * v s * φ s i) := by
          simp only [valFn, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro s hs
          ring
        have hproj (x : EuclideanSpace ℝ (Fin d)) (v : S → ℝ) :
            ∑ s, π s * valFn φ x s * projD π φ v s =
              ∑ s, π s * valFn φ x s * v s := by
          rw [hpair, hpair]
          simp_rw [hnormal]
        have hcs (u v : S → ℝ) :
            ∑ s, π s * u s * v s ≤ dNormV π u * dNormV π v := by
          have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
            (fun s => Real.sqrt (π s) * u s) (fun s => Real.sqrt (π s) * v s)
          have hm (s : S) : (Real.sqrt (π s) * u s) * (Real.sqrt (π s) * v s) =
              π s * u s * v s := by
            calc
              _ = (Real.sqrt (π s)) ^ 2 * u s * v s := by ring
              _ = _ := by rw [Real.sq_sqrt (hπ.1 s)]
          simpa only [hm, mul_pow, Real.sq_sqrt (hπ.1 _), dNormV] using hh
        have hsub (x y : EuclideanSpace ℝ (Fin d)) :
            valFn φ (x - y) = valFn φ x - valFn φ y := by
          ext s
          simp [valFn, inner_sub_right]
        intro θ
        let e := θstar - θ
        let w := projD π φ (H (valFn φ θstar)) - projD π φ (H (valFn φ θ))
        have hqnonneg : 0 ≤ dNormSq π φ e := by
          exact Finset.sum_nonneg (fun s hs => mul_nonneg (hπ.1 s) (sq_nonneg _))
        have hnormsq : dNormV π (valFn φ e) ^ 2 = dNormSq π φ e := by
          exact Real.sq_sqrt hqnonneg
        have hcn : dNormV π w ≤ c * dNormV π (valFn φ e) := by
          simpa only [e, w, hsub] using hcontr (valFn φ θstar) (valFn φ θ)
        have hbound : (∑ s, π s * valFn φ e s * w s) ≤ c * dNormSq π φ e := by
          calc
            _ ≤ dNormV π (valFn φ e) * dNormV π w := hcs _ _
            _ ≤ dNormV π (valFn φ e) * (c * dNormV π (valFn φ e)) :=
              mul_le_mul_of_nonneg_left hcn (Real.sqrt_nonneg _)
            _ = c * dNormSq π φ e := by rw [← hnormsq]; ring
        have hdir : ⟪e, gbarH π φ H θ⟫_ℝ =
            ∑ s, π s * valFn φ e s * (H (valFn φ θ) s - valFn φ θ s) := by
          simp only [gbarH, inner_sum, inner_smul_right]
          apply Finset.sum_congr rfl
          intro s hs
          rw [real_inner_comm]
          unfold valFn
          ring
        have heq : ⟪e, gbarH π φ H θ⟫_ℝ =
            dNormSq π φ e - ∑ s, π s * valFn φ e s * w s := by
          rw [hdir]
          have hp := hproj e (H (valFn φ θ))
          have hf (s : S) : projD π φ (H (valFn φ θstar)) s = valFn φ θstar s :=
            (congrFun hfix s).symm
          have he (s : S) : valFn φ e s = valFn φ θstar s - valFn φ θ s := by
            exact congrFun (hsub θstar θ) s
          dsimp only [w]
          have hsq : dNormSq π φ e = ∑ s, π s * valFn φ e s ^ 2 := rfl
          simp only [Pi.sub_apply, hf, hsq]
          simp only [mul_sub, Finset.sum_sub_distrib]
          rw [← hp]
          simp only [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s hs
          rw [he s]
          ring
        change (1 - c) * dNormSq π φ e ≤ _
        rw [heq]
        linarith
