-- Prove2me | solution 1 for BookProof.MixedLinearEsa.momentum_test_compactSupport_extend
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:05:22.729342+00:00
-- url     : https://prove2.me/submissions/8fa76c6a-c8c9-4c23-82a3-f6aee1a765e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.momentum_test_compactSupport_extend
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_exists_cutoff_seq
import Theorems.Thm_BookProof_MixedLinearEsa_hasCompactSupport_cutSchwartz
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_cutSchwartz
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.FourierMultiplierEsa

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


@[simp] private theorem cutSchwartz_apply (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) (x : V) :
    cutSchwartz g hg hgcs f x = ((g x : ℝ) : ℂ) * f x := rfl

set_option maxHeartbeats 1000000 in
theorem solution (m : V) (z : ℂ) (w : Lp ℂ 2 (volume : Measure V))
    (hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x))
    (f : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) ((momentumOp m f) x) * (w x)
      = z * ∫ x, (starRingEnd ℂ) (f x) * (w x) := by

  obtain ⟨cut, K, hsm, hcs, hb1, hev, hbK⟩ := exists_cutoff_seq (V := V)
  set fn : ℕ → 𝓢(V, ℂ) := fun n => cutSchwartz (cut n) (hsm n) (hcs n) f with hfn
  -- the identity along the cut-off sequence
  have key : ∀ n, ∫ x, (starRingEnd ℂ) ((momentumOp m (fn n)) x) * (w x)
      = z * ∫ x, (starRingEnd ℂ) ((fn n) x) * (w x) :=
    fun n => hw _ (hasCompactSupport_cutSchwartz (cut n) (hsm n) (hcs n) f)
  -- integrability of the two dominating pieces
  have hint1 : Integrable (fun x => (starRingEnd ℂ) ((momentumOp m f) x) * (w x))
      (volume : Measure V) := integrable_conj_schwartz_mul (momentumOp m f) w
  have hint2 : Integrable (fun x => (starRingEnd ℂ) (f x) * (w x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul f w
  have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (hbK 0 0)
  set bnd : V → ℝ := fun x => ‖(starRingEnd ℂ) ((momentumOp m f) x) * (w x)‖
      + (K * ‖m‖) * ‖(starRingEnd ℂ) (f x) * (w x)‖ with hbnd
  have hbndint : Integrable bnd (volume : Measure V) :=
    hint1.norm.add (hint2.norm.const_mul (K * ‖m‖))
  -- the left-hand sides converge
  have hL : Filter.Tendsto (fun n => ∫ x, (starRingEnd ℂ) ((momentumOp m (fn n)) x) * (w x))
      Filter.atTop (nhds (∫ x, (starRingEnd ℂ) ((momentumOp m f) x) * (w x))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence bnd
      (fun n => (integrable_conj_schwartz_mul (momentumOp m (fn n)) w).aestronglyMeasurable)
      hbndint (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [momentumOp_cutSchwartz m (cut n) (hsm n) (hcs n) f x]
      have hd : ‖((fderiv ℝ (cut n) x m : ℝ) : ℂ)‖ ≤ K * ‖m‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact le_trans ((fderiv ℝ (cut n) x).le_opNorm m)
          (mul_le_mul_of_nonneg_right (hbK n x) (norm_nonneg m))
      have hc1 : ‖((cut n x : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]
        exact hb1 n x
      calc ‖(starRingEnd ℂ) (-Complex.I * (f x * ((fderiv ℝ (cut n) x m : ℝ) : ℂ))
              + ((cut n x : ℝ) : ℂ) * (momentumOp m f x)) * (w x)‖
          ≤ ‖(starRingEnd ℂ) (-Complex.I * (f x * ((fderiv ℝ (cut n) x m : ℝ) : ℂ))) * (w x)‖
            + ‖(starRingEnd ℂ) (((cut n x : ℝ) : ℂ) * (momentumOp m f x)) * (w x)‖ := by
            rw [map_add, add_mul]
            exact norm_add_le _ _
        _ ≤ (K * ‖m‖) * ‖(starRingEnd ℂ) (f x) * (w x)‖
            + ‖(starRingEnd ℂ) ((momentumOp m f) x) * (w x)‖ := by
            gcongr ?_ + ?_
            · simp only [map_mul, norm_mul, RCLike.norm_conj, norm_neg, Complex.norm_I, one_mul]
              nlinarith [hd, norm_nonneg (f x), norm_nonneg (w x : ℂ),
                mul_nonneg (norm_nonneg (f x)) (norm_nonneg (w x : ℂ)),
                norm_nonneg (((fderiv ℝ (cut n) x m : ℝ) : ℂ))]
            · simp only [map_mul, norm_mul, RCLike.norm_conj]
              nlinarith [hc1, norm_nonneg ((momentumOp m f) x), norm_nonneg (w x : ℂ),
                mul_nonneg (norm_nonneg ((momentumOp m f) x)) (norm_nonneg (w x : ℂ)),
                norm_nonneg (((cut n x : ℝ) : ℂ))]
        _ = bnd x := by rw [hbnd]; ring
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev x] with n hn
      rw [momentumOp_cutSchwartz m (cut n) (hsm n) (hcs n) f x, hn.1]
      have h0 : fderiv ℝ (cut n) x m = 0 := by rw [hn.2]; rfl
      rw [h0]
      simp
  -- the right-hand sides converge
  have hR : Filter.Tendsto (fun n => ∫ x, (starRingEnd ℂ) ((fn n) x) * (w x))
      Filter.atTop (nhds (∫ x, (starRingEnd ℂ) (f x) * (w x))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖(starRingEnd ℂ) (f x) * (w x)‖)
      (fun n => (integrable_conj_schwartz_mul (fn n) w).aestronglyMeasurable)
      hint2.norm (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [hfn]
      simp only [cutSchwartz_apply, map_mul, norm_mul, RCLike.norm_conj, Complex.norm_real]
      nlinarith [hb1 n x, norm_nonneg (f x), norm_nonneg (w x : ℂ),
        mul_nonneg (norm_nonneg (f x)) (norm_nonneg (w x : ℂ)), norm_nonneg (cut n x)]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev x] with n hn
      rw [hfn]
      simp [hn.1]
  have hzR : Filter.Tendsto (fun n => z * ∫ x, (starRingEnd ℂ) ((fn n) x) * (w x))
      Filter.atTop (nhds (z * ∫ x, (starRingEnd ℂ) (f x) * (w x))) := hR.const_mul z
  exact tendsto_nhds_unique (by simpa only [key] using hL) hzR
