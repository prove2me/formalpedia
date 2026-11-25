-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.cutBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:27.779037+00:00
-- url     : https://prove2.me/submissions/c647445a-bd49-4dc7-bd38-3221380859f2

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59

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
theorem _root_.solution : CutBound := by
  intro c m p hm
  set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := (c.smooth.comp Real.contDiff_exp).pow m
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : Real.exp s ≤ 1/2 := by
        have := Real.exp_lt_exp.mpr hs
        rw [Real.exp_log (by norm_num)] at this; exact this.le
      simp only [hh, c.zero _ this]
      exact zero_pow (by omega)
    rw [this.iteratedDeriv_eq p, iterDeriv_const']; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, c.one _ this]
    rw [this.iteratedDeriv_eq p, iterDeriv_const']
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  have hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1 := by
    intro t
    rcases lt_or_ge t (Real.log (1/2)) with h1 | h1
    · rw [hlow t h1]; simp
    · rcases lt_or_ge 0 t with h2 | h2
      · rw [hhigh t h2]; split_ifs <;> simp
      · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)
  have key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε) := by
    intro ε x hε
    unfold ld
    have : (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε) := by
      funext u; simp only [hh, Cut.sc]; rw [Real.exp_sub, Real.exp_log hε]
    rw [this, iteratedDeriv_comp_sub_const]
  refine ⟨max C0 1, fun ε x hε hx => ?_⟩
  rw [key ε x hε]
  refine ⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩
  · rw [← Real.log_div hx.ne' hε.ne']
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hε]; linarith
  · have := Real.log_lt_log hε hlt; linarith
end Formalism.FourierDecayAlt.P.LEx1
