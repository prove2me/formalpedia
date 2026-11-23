-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.topOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:16.958796+00:00
-- url     : https://prove2.me/submissions/5444db42-8be3-43d6-8aad-aa5f88eeb618

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution (hA : J.PSDAgree) (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (hN0 : A5.BaseKernelOne)
    (h1 : A5.SingleBlockThetaProps) {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {un : Bool}
    (h : IsTopSys S Y un) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y ∧
      (un = true → ∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' =>
        (if t ∈ S.L then (1 : ℂ) else 0) - S.N t t h h')) := by
  obtain ⟨p, u, τ₀, η, m, hm, hun, hS⟩ := h
  obtain ⟨Θ, hu, -, hF⟩ := h1 p.K p.R p.ψ p.datum m
  have hΘ := hF (Y.image η) (by
    intro h hh; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh; exact hm x hx)
  have hSK := hS Θ hΘ.1 hu
  refine ⟨J.topSys p.R p.ψ p.σ u τ₀ η Θ, hTP hA p.K p.R p.ψ p.datum E (TB.Pt E) p.σ u τ₀ η Y Θ hΘ, hSK, ?_⟩
  intro hu' t ht
  have h2 := hTU hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) m p.σ u τ₀ η Y Θ hm (hun hu').1 (hun hu').2 hΘ t
  refine psd_congr ?_ h2
  intro x hx y hy
  rw [hSK.1 t t ht ht x hx y hy, hSK.2.2.1]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
