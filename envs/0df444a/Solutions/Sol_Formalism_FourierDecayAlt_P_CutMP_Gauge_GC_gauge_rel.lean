-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gauge_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:53.3178+00:00
-- url     : https://prove2.me/submissions/ede61bbb-b7f0-4e6f-92e3-4b4bba2fe59b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_trR_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution (hRef : GTCRef) (hPR : GTCPhaseRel) (hU : GTCConnUniq) (hCP : GTCConnPhase)
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hyp : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (A B : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hConn : ConnF P Bs d e A B) :
    ∃ (A0 : M.Ty P → ℂ → ℂ) (u : M.Ty P → ℂ → ℂ),
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A0 ρ) (Ann P)) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (u ρ ζ) * NF.dZ (u ρ) ζ) (Ann P)) ∧
      (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
      (∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n) ∧
      ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ := by
  obtain ⟨e0, he0, hk0, A0, B0, hAB0, hConn0, hcurv, hhol⟩ := hRef Wp Wq P Bs X d hyp
  obtain ⟨u, hu, heu⟩ := hPR Wp Wq P Bs X d hyp e e0 he hk he0 hk0
  obtain ⟨hAB1, hConn1⟩ := hCP Wp Wq P Bs X d hyp e0 A0 B0 u hAB0 hu hConn0
  have htr : trR P Bs (fun ρ ζ => u ρ ζ • e0 ρ ζ) = trR P Bs e :=
    trR_congr P Bs _ _ (fun ρ ζ hζ => (heu ρ ζ hζ).symm)
  have hConn1' : ConnF P Bs d e (fun ρ ζ => A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B0 ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
    unfold ConnF at hConn1 ⊢
    rw [← htr]
    exact hConn1
  have hA := hU Wp Wq P Bs X d hyp e he A B _ _ hAB hAB1 hConn hConn1'
  refine ⟨A0, u, fun ρ => (hAB0 ρ).1, hu, fun ρ => ?_, hcurv, hhol, hA⟩
  exact ((hAB1 ρ).1.sub (hAB0 ρ).1).congr (fun ζ _ => by ring)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
