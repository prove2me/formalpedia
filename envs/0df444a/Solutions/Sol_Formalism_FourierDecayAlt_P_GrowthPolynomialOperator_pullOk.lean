-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.pullOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:54.723143+00:00
-- url     : https://prove2.me/submissions/ab51c721-3628-4899-ab52-6812d4ceb3f7

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
theorem _root_.solution (hA : J.PSDAgree) (hA2 : A5.A2) (hLP : J.LocalPullback) (hPh : J.PhaseOk)
    (hUH : J.LocalUnitHeads) (hN0 : A5.BaseKernelOne)
    (h13 : ∀ s, 1 ≤ s → A5.A13 s) {S : J.LocSys E (TB.Pt E)} {Y : Finset (TB.Pt E)} {s : ℕ} {un : Bool}
    (hs : 1 ≤ s) (h : IsPull S Y s un) :
    ∃ S' : J.LocSys E (TB.Pt E), S'.Ok Y ∧ SameKernels S S' Y ∧
      (un = true → ∀ t : E, t ≠ 0 → TB.PSDOn Y (fun h h' =>
        (if t ∈ S.L then (1 : ℂ) else 0) - S.N t t h h')) := by
  obtain ⟨p, u, η, m, d, hm, hd, hun, hS⟩ := h
  obtain ⟨Θ, hΘ⟩ := h13 s hs p.K p.R p.ψ p.datum p.char0 m (Y.image η) (by
    intro h hh; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh; exact hm x hx)
  have hok := hLP hA hA2 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hs hm hΘ
  refine ⟨J.phaseSys d (J.pullSys p.R p.ψ s p.σ u η Θ), hPh E _ d _ Y hd hok, hS, ?_⟩
  intro hu t ht
  have h1 := hUH hA hN0 p.K p.R p.ψ p.datum E (TB.Pt E) s m p.σ u η Y Θ hm (hun hu) hΘ t ht
  refine psd_congr ?_ h1
  intro x hx y hy
  have hL : S.L = (J.pullSys p.R p.ψ s p.σ u η Θ).L := hS.2.2.1
  have hN := hS.1 t t ht ht x hx y hy
  rw [hN, hL]
  have hdd : d t * conj (d t) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd t]; simp
  simp only [J.phaseSys, hdd, one_mul]
  rfl
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
