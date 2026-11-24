-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.betaOnCut_of_tcritLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:54.842488+00:00
-- url     : https://prove2.me/submissions/9d385b36-f5ff-466b-88ed-3f71b2a0058b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_rho_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_prodb_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_edge_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_prod_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_prod_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_betaFactorisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_edgeFactorBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_nodeBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionAfter
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionsBefore
import Theorems.Thm_Formalism_FourierDecayAlt_P_slotAt_true

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
private lemma vthp_nonneg_of_ok (c : Cfg) (h : c.Ok) : 0 ≤ c.vthp := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)) hbp.le
  · exact le_refl _
end Formalism.FourierDecayAlt.P.Sz7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz7
theorem _root_.solution (HT : TcritLower) : BetaOnCut := by
  intro c r bb de de' ka rd g VV T T' Y l h hm hs hw hw' hrd hka hg hFD hT hT' hl hlk hne hY
  have hka0 : 0 < ka := by rw [hka]; exact div_pos (by positivity) (by linarith)
  have hg0 : 0 < g := by linarith [Real.pi_pos]
  have hA : 0 < (ka ^ (c.m - 1))⁻¹ := inv_pos.mpr (pow_pos hka0 _)
  have hB : 0 < (Real.sqrt (T * T'))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hT hT'))
  have hgm : 0 < g ^ c.m := pow_pos hg0 _
  obtain ⟨haeff, hUR⟩ := edge_bound c de de' Y l h hw hw' hl hlk hY
  have hP := prodb_pos c h
  have hv0 := vthp_nonneg_of_ok c h
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) (by linarith)
  have hfac := (betaFactorisation c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY).2.2.2
  have hsplit := prod_split (c.rho de de' (-Y)) c.k l hl hlk
  have hR0 := positionsBefore c de de' Y l h hw hw' hl hlk hY
  have hRl := (slotAt_true c de de' Y l h hw hw' hl hlk hne hY).2
  have hN := nodeBound c Y l h hl hlk hY
  have hRm : ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i ≤ 1 :=
    Finset.prod_le_one (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
      (fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact positionAfter c de de' Y l i h hw hw' hl (by omega) (by omega)
          (Or.inl (by omega)) hY)
  have hR00 : 0 ≤ ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRm0 : 0 ≤ ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRl0 := rho_nonneg c de de' Y l l h hlk hY
  have hRk0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hN0 : 0 ≤ c.Nd (-Y) := by
    unfold Cfg.Nd
    exact Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hU0 : 0 < c.U1 (-Y) := (edgeFactorBound c Y l h hl hlk hY).1
  have hsq : Real.sqrt (14 * (c.v l + Y) / (5 * c.Del)) =
      Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del) := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 14 / 5 by norm_num) ((c.v l + Y) / c.Del)]
    congr 1
    ring
  rw [hsq] at hRl
  have hT1 := HT c r bb de ka rd g VV h hm hs hw hrd hka hg hFD
  have hT2 := HT c r bb de' ka rd g VV h hm hs hw' hrd hka hg hFD
  have hQ0 : 0 < cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff :=
    div_pos (mul_pos (mul_pos (mul_pos hcOne hgm) hA) hP) haeff
  have htv : cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff *
      (Real.sqrt (T * T'))⁻¹ ≤ tv c de de' ka rd g VV T T' := by
    unfold tv
    rw [Real.le_sqrt' (mul_pos hQ0 hB), mul_pow, inv_pow, Real.sq_sqrt (mul_pos hT hT').le,
      div_eq_mul_inv (Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) *
        Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')))]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (mul_pos hT hT').le)
    rw [pow_two]
    exact mul_le_mul hT1 hT2 hQ0.le (hQ0.le.trans hT1)
  have hEP : 0 < Real.exp c.vth * c.prodb := mul_pos (Real.exp_pos _) hP
  have hsk : 0 ≤ Real.sqrt c.k := Real.sqrt_nonneg _
  have hsx : 0 ≤ Real.sqrt ((c.v l + Y) / c.Del) := Real.sqrt_nonneg _
  have hs5 : 0 ≤ Real.sqrt (14 / 5) := Real.sqrt_nonneg _
  have b1 := mul_le_mul hN hR0 hR00 hEP.le
  have b2 := mul_le_mul b1 hRl hRl0 (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
  have b3 := mul_le_mul b2 hRm hRm0
    (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk)) (mul_nonneg hs5 hsx))
  have b4 := mul_le_mul b3 hUR (mul_nonneg hU0.le hRk0)
    (mul_nonneg (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
      (mul_nonneg hs5 hsx)) (by norm_num))
  have hK : 0 ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ :=
    (mul_pos (mul_pos hgm hA) hB).le
  have hAZ : 0 ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb :=
    div_nonneg (by positivity) hcOne.le
  have hae := haeff.ne'
  have hco := hcOne.ne'
  rw [hfac, hsplit]
  calc g ^ c.m * ((ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ * c.Nd (-Y) * c.U1 (-Y) *
        ((∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * (c.rho de de' (-Y) l *
          ((∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) * c.rho de de' (-Y) (c.k - 1)))))
      = g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (c.Nd (-Y) * (∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * c.rho de de' (-Y) l *
          (∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) *
          (c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1))) := by ring
    _ ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (Real.exp c.vth * c.prodb * (3.3 * Real.sqrt c.k) *
          (Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del)) * 1 * (8 / c.aeff)) :=
        mul_le_mul_of_nonneg_left b4 hK
    _ = 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        (cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff * (Real.sqrt (T * T'))⁻¹) *
        Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) := by
        field_simp
    _ ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htv hAZ) hsk) hsx
    _ = AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
        Real.sqrt ((c.v l + Y) / c.Del) := rfl
end Formalism.FourierDecayAlt.P.Sz7
