-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:25.980178+00:00
-- url     : https://prove2.me/submissions/e6e24055-52a5-410f-8ca8-14aaeb2a6704

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_isUnit_det_of_bij
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dQ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dZ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_detId
import Theorems.Thm_Formalism_L2_Indef_twisted_finite
import Theorems.Thm_Formalism_L2_Indef_IndefRows_RR_spec
import Theorems.Thm_Formalism_L2_Indef_vw_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
namespace IndefRows
theorem _root_.solution [IsTotallyComplex K] (hB : StepBW) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric) (hRb : LemmaRb)
    (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF) (S : IndefRows Df)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w)) :
    (Function.support fun w => lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w)).Finite ∧
    lcv S.XE S.RR ≤ (S.D : ℝ) * meanLog S.κ + ∑ j, lcv (S.XW j) (S.M j) +
      ∑ᶠ w, lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w) := by
  have hdet0 := fun v => S.detId hS wf Bs.μ0 v (Or.inl rfl)
  have hdet1 := fun t => S.detId hS wf t Bs.v0 (Or.inr rfl)
  have hRR := S.RR_spec hG wf
  have hQ := S.dQ_eq
  have hZ := S.dZ_eq
  have hfr := S.frames
  have hc := S.l1c
  have h0 := S.h0
  have htw := twisted_finite S
  have hprov := S.proviso
  obtain ⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _p2, _p3, _g0, _g1, _g2, _g3, _g4⟩ := S
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only [DefSide.Proviso] at hdet0 hdet1 hRR hQ hZ hfr hc h0 htw hprov eb heb
  obtain rfl : dQ = fun _ => D := funext hQ
  obtain rfl : dZ = fun j _ => dW j := funext fun j => funext fun t => hZ j t
  exact hB K Bs.K0 wf.cm Bs.v0 wf.conj D XE hfr.1 Bs.Tup Bs.μ0 μ h0.1 htw XQ
    (fun t v => (wf.XQ_quot t v).1) (fun t => matLat (Pq t) (Mt t)) wf.Lam_lat ι
    (fun t => isUnit_det_of_bij _ (hc.1 t)) Bs.J dW XW hfr.2.1 M hfr.2.2 HT XT hprov wf.XT_herm Tl
    wf.Tl_lat θ (fun j t => isUnit_det_of_bij _ (hc.2.1 j t)) κ hc.2.2.1 (fun _ => 1) (fun _ => 1)
    (fun _ => by simp) rfl (fun _ => one_pos) (fun w => vw_one w) hdet0
    (fun t => by simpa only [mul_one] using hdet1 t)
    (fun t w => gramR (quotGram (Pq t) (HV t)) (eb t w)) eb heb
    (fun t w => (hR0 K Bs.K0 wf.cm Bs.v0 wf.conj (nV t) D (HV t) (wf.HV_rat t) (wf.HV_pos t) (Pq t)
      (wf.Pq_surj t) (XQ t) (wf.XQ_quot t) (eb t w)).2)
    (hRb K Bs.K0 wf.cm Bs.v0 wf.conj (nV Bs.μ0) D (HV Bs.μ0) (wf.HV_rat _) (wf.HV_pos _) (Pq Bs.μ0)
      (wf.Pq_surj _) (XQ Bs.μ0) (wf.XQ_quot _) (Mt Bs.μ0) (wf.Mt_lat _) (eb Bs.μ0) (heb Bs.μ0)).2
    _ hRR.1 hRR.2
end IndefRows
end Formalism.L2.Indef
