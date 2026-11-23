-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cauchy_theta_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:41.560594+00:00
-- url     : https://prove2.me/submissions/3ab21b43-3a3d-440d-8878-5edd668077c1

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_iteratedDeriv_ofReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_rpow_le_exp_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_base_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Complex Metric Set Formalism.FourierDecayAlt.P.Cauchy
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.E.CauchyTheta := by
  intro σ ε hσ hε p u
  have hσ0 : 0 < σ := by linarith
  set ρ : ℝ := 1 / (4 * σ) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : ρ ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le <;> linarith
  set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF
  set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf
  set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    fun_prop
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const (by fun_prop)
    exact Or.inl hw
  have hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x) := fun x => by positivity
  have hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ U := by
    intro x
    show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re
    rw [hcast, Complex.ofReal_re]
    exact hpos x
  have hfF : ∀ x : ℝ, F x = f x := by
    intro x
    show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _
    rw [hcast, ← Complex.ofReal_cpow (hpos x).le]
  have key := (iteratedDeriv_ofReal hU hFd hmem hfF p).2 u
  have hA : 0 < 1 + ε * Real.exp (-u) := hpos u
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hsub : closedBall (u : ℂ) ρ ⊆ U := by
    intro w hw
    have := base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    exact lt_of_lt_of_le h0 this
  have hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ) := by
    intro w hw
    have hb := base_bound hε u hρ (w := w) (by
      have : ‖w - u‖ = ρ := by simpa [dist_eq_norm] using hw
      exact this.le)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    have hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖ :=
      hb.trans (Complex.re_le_norm _)
    show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real]
    calc ‖1 + (ε : ℂ) * Complex.exp (-w)‖ ^ (-σ)
        ≤ ((1 + ε * Real.exp (-u)) * (1 - 2 * ρ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h0 hn (by linarith)
      _ = (1 + ε * Real.exp (-u)) ^ (-σ) * (1 - 2 * ρ) ^ (-σ) :=
          Real.mul_rpow hA.le h12.le
      _ ≤ (1 + ε * Real.exp (-u)) ^ (-σ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_exp_one hσ) (by positivity)
      _ = _ := mul_comm _ _
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0
    (hFd.diffContOnCl_ball hsub) hC
  rw [key, Complex.norm_real, Real.norm_eq_abs] at hcau
  refine hcau.trans (le_of_eq ?_)
  rw [hρdef, one_div, inv_pow, div_inv_eq_mul]
  ring
end Formalism.FourierDecayAlt.P
