-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.uu_eq_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:03.375587+00:00
-- url     : https://prove2.me/submissions/441e5a3a-22d5-43ea-b2ce-89a4464a9b9d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_ne_zero_of_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exp_br
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_br_mem_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_expI_th_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) (s : Bool) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    uu TT α ζ = Complex.exp (I * (th TT α (br s ζ) : ℂ)) := by
  unfold uu
  have h0 := ne_zero_of_An hTT hζ
  exact expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ)
    (by rw [Complex.exp_log h0, exp_br s h0])
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
