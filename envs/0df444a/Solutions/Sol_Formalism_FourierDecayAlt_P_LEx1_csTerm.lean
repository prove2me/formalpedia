-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.csTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:22.877201+00:00
-- url     : https://prove2.me/submissions/555911ca-8bc4-4ea5-a212-c28a42ace33a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_opt_delta
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pr_bound
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : CSTerm := by
  intro hTB hC B S σ ε h4 hε hM hW hI4 hI4' hCI Y hY p
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hEi : Integrable (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) B.μ := by
    have := hCI ε hε Y hY 0
    rwa [hds0] at this
  have hDi := hCI ε hε Y hY p
  have hfac : (0:ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  have hσ : 0 < 4 * σ := by linarith
  set K : ℝ := Real.exp 1 * p.factorial * (4 * σ) ^ p with hK
  have hKpos : 0 < K := by positivity
  have hE0 : 0 ≤ S.En ε σ Y := integral_nonneg fun ω => mul_nonneg (hth ω) (sq_nonneg' B _ hd _ ω)
  have hD0 : 0 ≤ S.Dn ε σ Y p := integral_nonneg fun ω => mul_nonneg (hth ω) (sq_nonneg' B _ hd _ ω)
  set I : ℂ := ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ with hI
  have hb : ∀ δ : ℝ, 0 < δ → ‖I‖ / K ≤ (S.En ε σ Y / δ + δ * S.Dn ε σ Y p) / 2 := by
    intro δ hδ
    have hg : Integrable (fun ω => K * (((th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) / δ +
        δ * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2)) B.μ :=
      (((hEi.div_const δ).add (hDi.const_mul δ)).div_const 2).const_mul K
    have h1 := norm_integral_le_of_norm_le hg (f := fun ω => (ld p (th ε σ) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω) (Eventually.of_forall fun ω => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have a1 := hTB hC σ ε h4 hε p (B.G ω) (B.G_pos ω)
      have a2 := pr_bound B (S.d Y) hd (S.gX Y) (S.ds Y p) δ hδ ω
      calc |ld p (th ε σ) (B.G ω)| * ‖pr B (S.d Y) (S.gX Y) (S.ds Y p) ω‖
          ≤ (K * th ε σ (B.G ω)) * ((LE.sq B (S.d Y) (S.gX Y) ω / δ + δ * LE.sq B (S.d Y) (S.ds Y p) ω) / 2) :=
            mul_le_mul a1 a2 (norm_nonneg _) (mul_nonneg hKpos.le (hth ω))
        _ = _ := by ring)
    have h2 : ∫ ω, K * (((th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) / δ +
        δ * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2) ∂B.μ =
        K * ((S.En ε σ Y / δ + δ * S.Dn ε σ Y p) / 2) := by
      rw [integral_const_mul, integral_div, integral_add (hEi.div_const δ) (hDi.const_mul δ), integral_div,
        integral_const_mul]
      rfl
    rw [h2] at h1
    rw [div_le_iff₀ hKpos]
    linarith
  have hfin := opt_delta _ _ _ hE0 hD0 hb
  rw [div_le_iff₀ hKpos] at hfin
  show ‖I / (p.factorial : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖I‖ ≤ √(S.En ε σ Y) * √(S.Dn ε σ Y p) * K := hfin
    _ = _ := by rw [hK]; ring
end Formalism.FourierDecayAlt.P.LEx1
