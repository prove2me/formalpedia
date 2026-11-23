-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.famOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:12.460861+00:00
-- url     : https://prove2.me/submissions/4240220d-ffe8-4096-bf5b-4602b8f5a517

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_pullOk
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_topOk
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_outOk

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
theorem _root_.solution (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne) (h13 : ∀ s, 1 ≤ s → A5.A13 s)
    (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (h1 : A5.SingleBlockThetaProps)
    (hSch : J.SchurProduct) (hPD : J.ProductDomination) (hOD : J.OutsideDomination)
    (hOS : J.OutsideSysOk) {W : Type} (D : TB.Data E W) (hD : LocalModel D)
    (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - s) :
    ∃ (P : Type) (_ : Fintype P) (S : P → J.LocSys E (TB.Pt E)) (a : TB.Pt E → ℝ),
      (∀ p, (S p).Ok Y) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf D i s).N t t' h h' = (J.scaleSys a (J.prodSys S)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf D i s).B h h' = (J.scaleSys a (J.prodSys S)).B h h') ∧
      (J.sysOf D i s).L = ⨅ p, (S p).L ∧ (⨅ p, (S p).L') ≤ (J.sysOf D i s).L' := by
  obtain ⟨P, _, S, a, hS, hN, hB, hL, hL'⟩ := hD.2.1 i s hs hsi hi Y hY
  have ex : ∀ p, ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels (S p) S' Y := by
    intro p
    rcases hS p with ⟨-, hT⟩ | ⟨-, hP⟩ | hO
    · obtain ⟨S', a, b, -⟩ := topOk hA hTP hTU hN0 h1 hT
      exact ⟨S', a, b⟩
    · obtain ⟨S', a, b, -⟩ := pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP
      exact ⟨S', a, b⟩
    · exact outOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS hs hO
  choose S' hok hSK using ex
  refine ⟨P, inferInstance, S', a, hok, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh'
    rw [hN t t' ht ht' h hh h' hh']
    simp only [J.scaleSys, J.prodSys]
    congr 1
    exact Finset.prod_congr rfl (fun p _ => (hSK p).1 t t' ht ht' h hh h' hh')
  · intro h hh h' hh'
    rw [hB h hh h' hh']
    simp only [J.scaleSys, J.prodSys]
    congr 1
    exact Finset.prod_congr rfl (fun p _ => (hSK p).2.1 h hh h' hh')
  · rw [hL]; exact iInf_congr (fun p => (hSK p).2.2.1)
  · have : (⨅ p, (S' p).L') = ⨅ p, (S p).L' := iInf_congr (fun p => ((hSK p).2.2.2).symm)
    rw [this]; exact hL'
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
