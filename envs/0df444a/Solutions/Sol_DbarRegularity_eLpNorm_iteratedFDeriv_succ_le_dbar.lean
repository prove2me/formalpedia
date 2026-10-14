-- Prove2me | solution 1 for DbarRegularity.eLpNorm_iteratedFDeriv_succ_le_dbar
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:25:50.43128+00:00
-- url     : https://prove2.me/submissions/03c2dce9-70f9-45e4-9915-b0d174ece5a7

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_DbarRegularity_norm_iteratedFDeriv_fderiv_apply_le
import Theorems.Thm_DbarRegularity_norm_iteratedFDeriv_succ_le_partials
import Theorems.Thm_DbarRegularity_dbar_fderiv_apply
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_euclidean



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal ContDiff

/-- Higher-order `L^p` estimate for the Cauchy–Riemann operator on the whole plane: for `1 < p`
there is `A` such that for every `j` and every smooth compactly supported `φ : ℂ → ℂⁿ`,
`‖D^{j+1} φ‖_{L^p} ≤ 2^j A ‖D^j (∂̄φ)‖_{L^p}`. -/
theorem eLpNorm_iteratedFDeriv_succ_le_dbar_aux (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ (j : ℕ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      HasCompactSupport φ →
      eLpNorm (iteratedFDeriv ℝ (j + 1) φ) (ENNReal.ofReal p) volume
        ≤ ((2 ^ j * A : ℝ≥0) : ℝ≥0∞)
          * eLpNorm (iteratedFDeriv ℝ j (dbar φ)) (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA⟩ := cauchyRiemann_lp_euclidean n p hp
  refine ⟨A, fun j => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hpart : ∀ (ψ : ℂ → EuclideanSpace ℂ (Fin n)) (w : ℂ), ContDiff ℝ ∞ ψ →
      ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z w) :=
    fun ψ w h => (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const
  have hpcs : ∀ (ψ : ℂ → EuclideanSpace ℂ (Fin n)) (w : ℂ), HasCompactSupport ψ →
      HasCompactSupport (fun z => fderiv ℝ ψ z w) :=
    fun ψ w h => (h.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] _ => L w) rfl
  have hdbar : ∀ ψ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ (dbar ψ) :=
    fun ψ h => (hpart ψ 1 h).add ((hpart ψ Complex.I h).const_smul Complex.I)
  have hdcs : ∀ ψ : ℂ → EuclideanSpace ℂ (Fin n), HasCompactSupport ψ →
      HasCompactSupport (dbar ψ) :=
    fun ψ h => by
      have h1 := hpcs ψ 1 h
      have h2 : HasCompactSupport (fun z => Complex.I • fderiv ℝ ψ z Complex.I) :=
        (hpcs ψ Complex.I h).comp_left (g := fun v => Complex.I • v) (smul_zero _)
      have h3 : dbar ψ = (fun z => fderiv ℝ ψ z 1) + (fun z => Complex.I • fderiv ℝ ψ z Complex.I) :=
        rfl
      rw [h3]
      exact h1.add h2
  -- splitting into the two partial derivatives, in `L^p`
  have tri : ∀ (m : ℕ) (ψ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ ψ →
      eLpNorm (iteratedFDeriv ℝ (m + 1) ψ) (ENNReal.ofReal p) volume
        ≤ eLpNorm (iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x 1)) (ENNReal.ofReal p) volume
          + eLpNorm (iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x Complex.I))
              (ENNReal.ofReal p) volume := by
    intro m ψ h
    have c1 := ((hpart ψ 1 h).continuous_iteratedFDeriv (m := m) (mod_cast le_top)).norm
    have c2 := ((hpart ψ Complex.I h).continuous_iteratedFDeriv (m := m) (mod_cast le_top)).norm
    calc eLpNorm (iteratedFDeriv ℝ (m + 1) ψ) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun z => ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x 1) z‖
            + ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x Complex.I) z‖)
            (ENNReal.ofReal p) volume := by
          apply eLpNorm_mono_real
          intro z
          exact norm_iteratedFDeriv_succ_le_partials m (h.of_le (mod_cast le_top)) z
      _ ≤ eLpNorm (fun z => ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x 1) z‖)
            (ENNReal.ofReal p) volume
          + eLpNorm (fun z => ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x Complex.I) z‖)
            (ENNReal.ofReal p) volume :=
          eLpNorm_add_le c1.aestronglyMeasurable c2.aestronglyMeasurable hp1
      _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]
  -- dropping a unit directional derivative
  have drop : ∀ (m : ℕ) (ψ : ℂ → EuclideanSpace ℂ (Fin n)) (w : ℂ), ‖w‖ = 1 →
      ContDiff ℝ ∞ ψ →
      eLpNorm (iteratedFDeriv ℝ m (fun x => fderiv ℝ ψ x w)) (ENNReal.ofReal p) volume
        ≤ eLpNorm (iteratedFDeriv ℝ (m + 1) ψ) (ENNReal.ofReal p) volume := by
    intro m ψ w hw h
    apply eLpNorm_mono
    intro z
    have := norm_iteratedFDeriv_fderiv_apply_le m (h.of_le (mod_cast le_top)) w z
    rwa [hw, one_mul] at this
  -- zeroth derivative
  have zero : ∀ ψ : ℂ → EuclideanSpace ℂ (Fin n),
      eLpNorm (iteratedFDeriv ℝ 0 ψ) (ENNReal.ofReal p) volume
        = eLpNorm ψ (ENNReal.ofReal p) volume :=
    fun ψ => eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun z => norm_iteratedFDeriv_zero)
  induction j with
  | zero =>
    intro φ h hcs
    have hφ1 : ContDiff ℝ 1 φ := h.of_le (mod_cast le_top)
    calc eLpNorm (iteratedFDeriv ℝ (0 + 1) φ) (ENNReal.ofReal p) volume
        ≤ _ := tri 0 φ h
      _ = eLpNorm (fun x => fderiv ℝ φ x 1) (ENNReal.ofReal p) volume
          + eLpNorm (fun x => fderiv ℝ φ x Complex.I) (ENNReal.ofReal p) volume := by
          rw [zero, zero]
      _ ≤ A * eLpNorm (dbar φ) (ENNReal.ofReal p) volume := hA φ hφ1 hcs
      _ = _ := by rw [zero]; simp
  | succ m ih =>
    intro φ h hcs
    have h2 : ContDiff ℝ 2 φ := h.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    have key : ∀ w : ℂ, ‖w‖ = 1 →
        eLpNorm (iteratedFDeriv ℝ (m + 1) (fun x => fderiv ℝ φ x w)) (ENNReal.ofReal p) volume
          ≤ ((2 ^ m * A : ℝ≥0) : ℝ≥0∞)
            * eLpNorm (iteratedFDeriv ℝ (m + 1) (dbar φ)) (ENNReal.ofReal p) volume := by
      intro w hw
      refine (ih _ (hpart φ w h) (hpcs φ w hcs)).trans ?_
      rw [dbar_fderiv_apply h2 w]
      gcongr
      exact drop m (dbar φ) w hw (hdbar φ h)
    calc eLpNorm (iteratedFDeriv ℝ (m + 1 + 1) φ) (ENNReal.ofReal p) volume
        ≤ _ := tri (m + 1) φ h
      _ ≤ ((2 ^ m * A : ℝ≥0) : ℝ≥0∞)
            * eLpNorm (iteratedFDeriv ℝ (m + 1) (dbar φ)) (ENNReal.ofReal p) volume
          + ((2 ^ m * A : ℝ≥0) : ℝ≥0∞)
            * eLpNorm (iteratedFDeriv ℝ (m + 1) (dbar φ)) (ENNReal.ofReal p) volume :=
          add_le_add (key 1 (by simp)) (key Complex.I (by simp))
      _ = _ := by push_cast; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem solution (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ (j : ℕ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      HasCompactSupport φ →
      eLpNorm (iteratedFDeriv ℝ (j + 1) φ) (ENNReal.ofReal p) volume
        ≤ ((2 ^ j * A : ℝ≥0) : ℝ≥0∞)
          * eLpNorm (iteratedFDeriv ℝ j (dbar φ)) (ENNReal.ofReal p) volume :=
  eLpNorm_iteratedFDeriv_succ_le_dbar_aux n p hp
