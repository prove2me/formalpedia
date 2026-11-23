-- Prove2me | solution 1 for Formalism.L2.Th1.H.LineTransport_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:52.957808+00:00
-- url     : https://prove2.me/submissions/2ce81738-1d8e-4b7d-b113-07a95485f76e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Theorems.Thm_Formalism_L2_Th1_H_Inv_inter_smul
import Theorems.Thm_Formalism_L2_Th1_H_Inv_inter_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Inv
namespace Formalism.L2.Th1.H
theorem _root_.solution (hinv : InterInv) (hth : InterTh) : LineTransport := by
  intro V _ _ _ H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 θ₁ hθ₁ hne hline
  have hθ' : AnalyticOnNhd ℂ θ₁ Set.univ ∧ θ₁ ∈ fixedBy H α Λ₁ := hθ₁
  refine ⟨fun h0 => hne ?_, fun F hF => ?_⟩
  · funext z
    have h := hinv V H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 θ₁ hθ'.2 z
    rw [h0, Formalism.L2.Th1.H.Inv.inter_zero] at h
    simpa using h.symm
  · have hF' : AnalyticOnNhd ℂ F Set.univ ∧ F ∈ fixedBy H α Λ₂ := hF
    obtain ⟨c, hc⟩ := hline _ (hth V H hH Λ₂ Λ₁ α hα₁ h21 F hF)
    refine ⟨c, funext fun z => ?_⟩
    rw [← hinv V H hH Λ₂ Λ₁ α h₂ h₁ hα₂ hα₁ h21 h12 F hF'.2 z, hc, Formalism.L2.Th1.H.Inv.inter_smul]
end Formalism.L2.Th1.H
