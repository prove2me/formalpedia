-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:18.040962+00:00
-- url     : https://prove2.me/submissions/e178105c-10fc-4389-a0a6-668932b0d2c9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_hess_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_fderiv_le
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_norm_dirv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {d : ℕ} {φ : (Fin d → ℂ) → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ c₁ ρ : ℝ}
    (hr : 0 < r) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    (hl : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|)
    (hρr : ρ ≤ r) (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n * ρ ≤ c₁ / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, ∃ l : Fin d × Bool,
      c₁ / 2 * ‖x‖ ≤ |fderiv ℝ (fun y => quad φ y + s * E_P φ y) x (dirv l)| := by
  intro x hx
  have hxr : x ∈ Metric.closedBall (0 : Fin d → ℂ) r := Metric.closedBall_subset_closedBall hρr hx
  have hxρ : ‖x‖ ≤ ρ := by simpa using hx
  obtain ⟨l, hl⟩ := hl x hxr
  refine ⟨l, ?_⟩
  rw [E_ph_fderiv' (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n)))]
  have h1 := E_P_fderiv_le h3n hφ hr hc hb hxr
  set K := (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n with hK
  have hK0 : 0 ≤ K := by
    have hΓ : 0 ≤ Γ := (norm_nonneg _).trans (E_hess_le (by omega : 2 ≤ n) hr hb)
    positivity
  have h2 : |fderiv ℝ (E_P φ) x (dirv l)| ≤ K * ‖x‖ ^ 2 := by
    have := (fderiv ℝ (E_P φ) x).le_opNorm (dirv l)
    rw [E_norm_dirv, mul_one, Real.norm_eq_abs] at this
    exact this.trans h1
  have a1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have h3 : |(1 - s) * fderiv ℝ (E_P φ) x (dirv l)| ≤ K * ‖x‖ ^ 2 := by
    rw [abs_mul]
    calc |1 - s| * |fderiv ℝ (E_P φ) x (dirv l)| ≤ 1 * (K * ‖x‖ ^ 2) :=
          mul_le_mul a1 h2 (abs_nonneg _) zero_le_one
      _ = K * ‖x‖ ^ 2 := one_mul _
  have h4 : K * ‖x‖ ^ 2 ≤ c₁ / 2 * ‖x‖ := by
    have : K * ‖x‖ ≤ c₁ / 2 := (mul_le_mul_of_nonneg_left hxρ hK0).trans hρ
    nlinarith [norm_nonneg x]
  have h5 := abs_sub_abs_le_abs_sub (fderiv ℝ φ x (dirv l)) ((1 - s) * fderiv ℝ (E_P φ) x (dirv l))
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
