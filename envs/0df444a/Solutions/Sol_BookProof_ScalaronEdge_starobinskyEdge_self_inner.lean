-- Prove2me | solution 1 for BookProof.ScalaronEdge.starobinskyEdge_self_inner
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:20:47.664159+00:00
-- url     : https://prove2.me/submissions/15dba3ff-5c0a-4771-b908-d49ac3e0b048

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.starobinskyEdge_self_inner
import Mathlib
import Definitions.Def_ChapterScalaronEdge
open BookProof.ScalaronEdge









open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
/-- The `L²` square of a core vector, as an ordinary integral.

`ccEquiv ℝ` is `LinearEquiv.ofInjective (ccInclLM ℝ)`, so the underlying `L²` element of
`ccEquiv ℝ f` is definitionally `(f : 𝓢(ℝ, ℂ)).toLp 2 volume`.  The `L²` inner product of
two Schwartz classes is the integral of the pointwise inner products
(`SchwartzMap.inner_toL2_toL2_eq`), and pointwise `⟪z, z⟫_ℂ = (‖z‖ : ℂ) ^ 2`
(`inner_self_eq_norm_sq_to_K`); pulling the real cast out of the integral
(`integral_complex_ofReal`) finishes.

Note on the pointwise step: `inner_self_eq_norm_sq_to_K` produces the coercion
`RCLike.ofReal ‖z‖ : ℂ`, while `Complex.ofReal_pow` produces `Complex.ofReal ‖z‖`.  The two
agree by `RCLike.ofReal_eq_complex_ofReal`, which is `rfl` at *default* transparency only,
so the closing `rfl` that `rw` itself runs (`with_reducible rfl`) leaves the goal
`↑‖f x‖ ^ 2 = ↑‖f x‖ ^ 2` open; an explicit `rfl` afterwards discharges it. -/
theorem solution (f : ccSchwartz ℝ) :
    (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by
  have hcoe : ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))
      = (f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ) := by
    first
      | rfl
      | simp [ccEquiv, ccInclLM]
  have hinner : (inner ℂ ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ))
        ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ)) : ℂ)
      = ∫ x, (inner ℂ ((f : 𝓢(ℝ, ℂ)) x) ((f : 𝓢(ℝ, ℂ)) x) : ℂ) := by
    first
      | exact SchwartzMap.inner_toL2_toL2_eq _ _ _
      | exact SchwartzMap.inner_toL2_toL2_eq (f : 𝓢(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ))
          (volume : Measure ℝ)
      | simp
  have hpt : ∀ x : ℝ, (inner ℂ ((f : 𝓢(ℝ, ℂ)) x) ((f : 𝓢(ℝ, ℂ)) x) : ℂ)
      = ((‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    first
      | (rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; done)
      | (rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl)
      | (rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow];
         exact congrArg (· ^ 2) (congrFun RCLike.ofReal_eq_complex_ofReal _))
      | (rw [RCLike.inner_apply', Complex.conj_mul', Complex.ofReal_pow]; done)
      | (rw [RCLike.inner_apply', Complex.conj_mul', Complex.ofReal_pow]; rfl)
      | (simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; done)
      | (simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl)
      | (simp only [RCLike.inner_apply', Complex.conj_mul', Complex.ofReal_pow]; done)
      | (simp only [RCLike.inner_apply', Complex.conj_mul', Complex.ofReal_pow]; rfl)
      | (simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; done)
  have hint : (∫ x, (inner ℂ ((f : 𝓢(ℝ, ℂ)) x) ((f : 𝓢(ℝ, ℂ)) x) : ℂ))
      = ∫ x, ((‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
  rw [hcoe, hinner, hint]
  first
    | exact integral_complex_ofReal
    | exact integral_ofReal
    | simp [integral_complex_ofReal]
