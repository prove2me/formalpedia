-- Prove2me | solution 1 for Formalism.L2.Indef.IndefSide.boundsMu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:19.242833+00:00
-- url     : https://prove2.me/submissions/cdad5c0d-0e00-4214-8672-a2b4e0567af6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_isUnit_det_of_bij
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dQ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dZ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dW_eq
import Theorems.Thm_Formalism_L2_Indef_IndefRows_D_pos
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
namespace IndefSide
theorem _root_.solution [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) {Bs : DefBase K} {Df : DefSide Bs} {N : IndefNum Bs} (wf : Df.WF)
    (S : IndefSide Df N) (hU : S.toIndefData.Untwisted N)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : S.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df.Gm eb (S.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df.Gm eb (S.μ y) y) : ℝ) ≤ (S.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ S.Tw, ∀ j, (jw (Df.HT j (S.μ y)) y (Df.Tl j (S.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (S.μ y) y j) * (S.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ S.Tw, lw y * ηy y j / (S.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3) :
    Formalism.HN.muDef (Pi.basisFun K (Fin S.D)).dualBasis (Formalism.HN.dualFrame S.XE) (Formalism.HN.dualLat S.RR) ≤
      meanLog S.κ + (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ S.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
        (∑ j, (N.E1 j + E2 j)) + E3 := by
  have hdet0 := fun v => S.toIndefRows.detId hS wf Bs.μ0 v (Or.inl rfl)
  have hdet1 := fun t => S.toIndefRows.detId hS wf t Bs.v0 (Or.inr rfl)
  have hRR := S.toIndefRows.RR_spec hG wf
  have hQ := S.toIndefRows.dQ_eq
  have hZ := S.toIndefRows.dZ_eq
  have hW := S.toIndefRows.dW_eq wf
  have hD := S.toIndefRows.D_pos
  have hfr := S.frames
  have hc := S.l1c
  have hl3 := S.l3
  have hon := S.on
  have h0 := S.h0
  have htw := twisted_finite S.toIndefRows
  have hprov := S.proviso
  have hout : ∀ y, y ∉ Sy → lw y * ((vw y (Df.Gm eb (S.μ y) y) : ℝ) + ∑ j, S.Aw j y) = 0 := by
    intro y hy
    rw [hG0 y hy, Finset.sum_eq_zero fun j _ => (hU y (fun h => hy (hSy h)) j).1]
    simp
  have hmid : ∀ y ∈ Sy, y ∉ S.Tw → ∀ j, S.Aw j y = 0 := fun y _ hy j => (hU y hy j).1
  have hF : ∀ y ∈ Sy, y ∉ S.Tw → ∀ j, (ramw y : ℝ) * N.F0 y j = 0 := fun y _ hy j => by
    rw [(hU y hy j).2, mul_zero]
  have hiii : ∀ y ∈ S.Tw, ∑ j, ((S.Iw j (S.μ y) y : ℝ) + (S.Iw j (S.μ y) (conjPl y) : ℝ)) ≤
      (∑ j, (2 * ((ramw y : ℝ) * N.F0 y j) + (ramw y : ℝ) * S.err0 y j) + 2 / ellw y ^ 2) * (S.D : ℝ) := by
    intro y hy
    rw [(hRam K y).2.2.2.2]
    exact hon.1 y hy
  obtain ⟨⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _p2, _p3, _g0, _g1, _g2, _g3, _g4⟩, _g6, _g7⟩ := S
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only [DefSide.Proviso] at hdet0 hdet1 hRR hQ hZ hW hD hfr hc hl3 hon h0 htw hprov hout hmid hF hiii eb heb hi hiv hE2 hG0 hSy hLG hE3
  obtain rfl : dW = fun _ => D := funext hW
  obtain rfl : dQ = fun _ => D := funext hQ
  obtain rfl : dZ = fun _ _ => D := funext fun j => funext fun t => hZ j t
  have H := (hM K Bs.K0 wf.cm Bs.v0 wf.conj D XE hD hfr.1 Bs.Tup Bs.μ0 μ h0.1 htw XQ
    (fun t v => (wf.XQ_quot t v).1) (fun t => matLat (Pq t) (Mt t)) wf.Lam_lat ι
    (fun t => isUnit_det_of_bij _ (hc.1 t)) Bs.J XW hfr.2.1 M hfr.2.2 HT XT hprov wf.XT_herm Tl
    wf.Tl_lat θ (fun j t => isUnit_det_of_bij _ (hc.2.1 j t)) κ hc.2.2.1 (fun _ => 1) (fun _ => 1)
    (fun _ => by simp) rfl (fun _ => one_pos) (fun w => vw_one w) hdet0
    (fun t => by simpa only [mul_one] using hdet1 t)
    (fun t w => gramR (quotGram (Pq t) (HV t)) (eb t w)) eb heb
    (fun t w => (hR0 K Bs.K0 wf.cm Bs.v0 wf.conj (nV t) D (HV t) (wf.HV_rat t) (wf.HV_pos t) (Pq t)
      (wf.Pq_surj t) (XQ t) (wf.XQ_quot t) (eb t w)).2)
    (nV Bs.μ0) (HV Bs.μ0) (wf.HV_rat _) (wf.HV_pos _) (Pq Bs.μ0) (wf.Pq_surj _) (wf.XQ_quot _) (Mt Bs.μ0)
    (wf.Mt_lat _) rfl (fun _ => rfl) _ hRR.1 hRR.2 Sy Tw hSy hout hmid LG E3 N.E1 E2 ellw gy
    (fun y j => (ramw y : ℝ) * N.F0 y j) (fun y j => (ramw y : ℝ) * err0 y j)
    (fun y j => (ramw y : ℝ) * N.J0 (μ y) y j) ηy hF hi hLG hiii hiv hon.2.2 hE2 hE3).1
  have h3 : ∑ j, lcv (XW j) (M j) / (D : ℝ) ≤ ∑ j, N.l3 j := Finset.sum_le_sum fun j _ => hl3 j
  linarith [H, h3]
end IndefSide
end Formalism.L2.Indef
