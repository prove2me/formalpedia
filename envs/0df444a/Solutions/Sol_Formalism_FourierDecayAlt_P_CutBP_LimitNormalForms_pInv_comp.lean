-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.pInv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:45.55417+00:00
-- url     : https://prove2.me/submissions/585c5308-a51f-43a4-807b-6cefe12ee60e

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_of_smoothLev
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyOp_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {o₁ κ₁ o₂ κ₂ : ℕ} {Θ₁ Θ₂ : B.DiffOp P.k P.r Wp Wq} (h₁ : PInv P Bs o₁ κ₁ Θ₁)
    (h₂ : PInv P Bs o₂ κ₂ Θ₂) : ∃ Θ : B.DiffOp P.k P.r Wp Wq, PInv P Bs (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      ∀ J ∈ FFB P Bs, ∀ g ∈ B.GV P.k P.r ∩ Gauge.OmB Bs, B.opApply Θ J g = B.opApply Θ₁ (B.opApply Θ₂ J) g := by
  obtain ⟨Θ, hP, hl, hc⟩ := polyOp_comp h₁.1 h₂.1
  refine ⟨Θ, ⟨hP, hc Bs {g | 0 < Gf P.k P.r Bs.z Bs.z' g} (isOpen_lt continuous_const (BetaSesquilinearity.Gf_cont _ _)) h₁.2 h₂.2⟩,
    fun J hJ g hg => hl _ J (BetaSesquilinearity.sCkOn_mono le_top (ck_of_smoothLev hJ.1)) g hg hg.1⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
