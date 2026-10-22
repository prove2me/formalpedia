-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:30:40.658889+00:00
-- url     : https://prove2.me/submissions/fe4df725-6690-4169-8256-817161776e68

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_inc
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_radialFactor_eval
import Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_u_spherePt_inc
import Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_v_spherePt_inc
import Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_e_spherePt_inc
import Theorems.Thm_BookProof_ChapterSolidHarmonic_norm_spherePt_inc
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace
open BookProof.ChapterLegendrePolynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

set_option maxHeartbeats 1000000 in

include he hu hue huv hv hve in
theorem solution {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) (φ : ℝ) :
    solidHarmonic u v e l μ (spherePt u v e r θ φ)
      = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) := by
  set x := spherePt u v e r θ φ with hx
  have hnorm : ‖x‖ = r := norm_spherePt_inc hu hv he huv hue hve hr.le θ φ
  have hxne : x ≠ 0 := by
    intro hcon
    rw [hcon] at hnorm
    simp at hnorm
    exact absurd hnorm.symm (ne_of_gt hr)
  have hiu : ⟪u, x⟫_ℝ = r * Real.sin θ * Real.cos φ := inner_u_spherePt_inc hu hv he huv hue hve r θ φ
  have hiv : ⟪v, x⟫_ℝ = r * Real.sin θ * Real.sin φ := inner_v_spherePt_inc hu hv he huv hue hve r θ φ
  have hie : ⟪e, x⟫_ℝ = r * Real.cos θ := inner_e_spherePt_inc hu hv he huv hue hve r θ φ
  -- the angular factor
  have hw : nullCLM u v x = ((r * Real.sin θ : ℝ) : ℂ) * Complex.exp (φ * Complex.I) := by
    rw [nullCLM_apply, hiu, hiv, Complex.exp_mul_I]
    push_cast
    ring
  have hang : angular u v μ x = (r * Real.sin θ) ^ μ * Real.cos (μ * φ) := by
    have hcast : (((r * Real.sin θ : ℝ) : ℂ)) ^ μ = (((r * Real.sin θ) ^ μ : ℝ) : ℂ) := by
      push_cast; ring
    rw [angular, hw, mul_pow, ← Complex.exp_nat_mul, hcast,
      show (μ : ℂ) * (φ * Complex.I) = ((μ : ℝ) * φ : ℝ) * Complex.I from by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- the radial factor
  have hrad : radialFactor e l μ x
      = r ^ (l - μ) * (derivative^[μ] (legendre l)).eval (Real.cos θ) := by
    rw [radialFactor_eval e hμ hxne, hnorm, hie]
    congr 2
    field_simp
  have hsin : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 from by
      have := Real.sin_sq_add_cos_sq θ; linarith]
    exact Real.sqrt_sq hθ
  rw [solidHarmonic, hang, hrad, assocLegendre, hsin]
  have hrl : r ^ μ * r ^ (l - μ) = r ^ l := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow]
  ring_nf
  rw [show r ^ μ * r ^ (l - μ) = r ^ l from hrl]
