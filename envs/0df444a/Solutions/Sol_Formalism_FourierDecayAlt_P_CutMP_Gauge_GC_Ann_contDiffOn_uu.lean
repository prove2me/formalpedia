-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.contDiffOn_uu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:33.966836+00:00
-- url     : https://prove2.me/submissions/1f1c93a2-1b47-4dce-8389-df09ed76b37e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_br_mem_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_contDiffAt_br
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_contDiffOn_th
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exists_br
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_ne_zero_of_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_uu_eq_br


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
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uu TT α) (An TT) := by
  intro ζ hζ
  obtain ⟨s, hs⟩ := exists_br (ne_zero_of_An hTT hζ)
  have hev : uu TT α =ᶠ[𝓝 ζ] fun z => Complex.exp (I * (th TT α (br s z) : ℂ)) := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (br s ζ) :=
    (contDiffOn_th hTT hα hcurv).contDiffAt ((isOpen_Hh TT).mem_nhds (br_mem_Hh s hTT hζ))
  have hbr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ :=
    (contDiffAt_br s hs).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((th TT α (br s z) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hth.comp ζ hbr)
  exact ((contDiffAt_const.mul h2).cexp.congr_of_eventuallyEq hev).contDiffWithinAt
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
