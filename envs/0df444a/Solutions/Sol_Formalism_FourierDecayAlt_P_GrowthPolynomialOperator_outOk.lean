-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.outOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:59.855696+00:00
-- url     : https://prove2.me/submissions/d87ffcdb-b2ff-4114-8c42-ea7f20d71833

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_pullOk
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_topOk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add
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
theorem _root_.solution (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne) (h13 : ∀ s, 1 ≤ s → A5.A13 s)
    (hTP : J.TopPullback) (hTU : J.TopUnitHeads) (h1 : A5.SingleBlockThetaProps)
    (hSch : J.SchurProduct) (hPD : J.ProductDomination) (hOD : J.OutsideDomination)
    (hOS : J.OutsideSysOk)
    {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {s : ℕ} {tp : Prop}
    (hs : 1 ≤ s) (h : IsOut S Y s tp) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y := by
  obtain ⟨hB, hF⟩ := h
  have fac : ∀ F : J.LocSys E (TB.Pt E), ((tp ∧ IsTopSys F Y true) ∨ (¬ tp ∧ IsPull F Y s true)) →
      ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels F S' Y ∧
      (∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' => (if t ∈ F.L then (1 : ℂ) else 0) - F.N t t h h')) := by
    intro F hF
    rcases hF with ⟨-, hT⟩ | ⟨-, hP⟩
    · obtain ⟨S', a, b, c⟩ := topOk hA hTP hTU hN0 h1 hT
      exact ⟨S', a, b, c rfl⟩
    · obtain ⟨S', a, b, c⟩ := pullOk hA hA2 hLP hPh hUH hN0 h13 hs hP
      exact ⟨S', a, b, c rfl⟩
  refine ⟨J.LocSys.mk S.N (fun t _ _ => if t ∈ S.L then 1 else 0) (fun _ _ => 1) S.L S.L',
    hOS E (TB.Pt E) S.N S.L S.L' Y ?_ ?_ ?_, ⟨fun _ _ _ _ _ _ _ _ => rfl, hB, rfl, rfl⟩⟩
  · intro t t' ht ht' h hh h' hh' hne
    obtain ⟨Q, _, F, hQ, hN, -, hL'⟩ := hF t t' ht ht'
    apply hL'
    intro q
    obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
    rw [hSK.2.2.2]
    apply hok.1 t t' ht ht' h hh h' hh'
    rw [← hSK.1 t t' ht ht' h hh h' hh']
    intro h0
    apply hne
    rw [hN h hh h' hh']
    exact Finset.prod_eq_zero (Finset.mem_univ q) h0
  · intro t ht
    obtain ⟨Q, _, F, hQ, hN, -, -⟩ := hF t t ht ht
    have := hSch (TB.Pt E) Q Y (fun q => (F q).N t t) (by
      intro q
      obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
      exact psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht))
    exact psd_congr (fun x hx y hy => (hN x hx y hy).symm) this
  · intro t ht
    obtain ⟨Q, _, F, hQ, hN, hL, -⟩ := hF t t ht ht
    have key := hOD hPD E (TB.Pt E) Q (fun q => (F q).N t t) (fun q => (F q).L) t Y (by
      intro q
      obtain ⟨S', hok, hSK, -⟩ := fac (F q) (hQ q)
      exact psd_congr (fun x hx y hy => (hSK.1 t t ht ht x hx y hy).symm) (hok.2.1 t ht)) (by
      intro q
      obtain ⟨S', -, -, hd⟩ := fac (F q) (hQ q)
      exact hd t ht)
    by_cases hin : t ∈ ⨅ q, (F q).L
    · have hS : t ∈ S.L := hL (fun q => (AddSubgroup.mem_iInf.1 hin) q)
      refine psd_congr ?_ key
      intro x hx y hy
      simp only [hin, hS, if_true, hN x hx y hy]
    · by_cases hS : t ∈ S.L
      · have := psd_add (psd_one hSch Y) key
        refine psd_congr ?_ this
        intro x hx y hy
        simp only [hin, hS, if_true, if_false, hN x hx y hy]
        ring
      · refine psd_congr ?_ key
        intro x hx y hy
        simp only [hin, hS, if_false, hN x hx y hy]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
