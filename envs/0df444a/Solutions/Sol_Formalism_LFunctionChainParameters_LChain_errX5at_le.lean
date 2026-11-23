-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.errX5at_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:48.85014+00:00
-- url     : https://prove2.me/submissions/271942c2-7cb5-48ff-bf52-df64d70d56e8

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_core_ineq
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_inv_one_sub_le_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_log_le_of_le_rpow
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_log_one_add_rpow_le
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_sub_three_mul_log_two_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (hW : ErrWindows D C Xpp eK K) (hX : LargeX D.x D.ε K C.cHH eK) (u0 : U0) :
    ErrX5at D C Xpp u0 ≤ D.x ^ (CErr C * D.ε) * ErrText D := by
  obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  obtain ⟨hlog, hbig⟩ := hX
  have hx0 : 0 < D.x := by linarith only [hx]
  have hy : 1 ≤ D.x ^ D.ε := Real.one_le_rpow hx hε.le
  have hyD : 1 ≤ D.x ^ (C.eDiv * D.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
  have hyL : 1 ≤ D.x ^ (C.eLoss * D.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have hbxb : D.b ≤ D.x * D.b := le_mul_of_one_le_left hb0 hx
  have hba : D.b ≤ D.a := hbxb.trans hxb
  have ha1 : 1 ≤ D.a := hb.trans hba
  have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk : 0 < D.k := by linarith only [hk1]
  have hmx : (m : ℝ) ≤ D.x := by
    refine hm.trans ?_
    calc D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ≤ D.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
      _ = D.x := Real.rpow_one _
  have hMk : (m : ℝ) ≤ D.k := (le_mul_of_one_le_left hM hx).trans hxm
  have hMb : (m : ℝ) * D.b ≤ D.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
  have hsA0 : 0 ≤ D.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
  have hsA : D.sumA ≤ 2 * (D.nT * D.a) := by
    unfold Data.sumA Data.nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, 2 * D.a := Finset.sum_le_sum (fun t _ => (haT t).2)
      _ = 2 * ((Fintype.card Top : ℝ) * D.a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlWk : Real.log (Fintype.card (W u0) : ℝ) ≤ D.a :=
    ((hlW u0).trans (sub_three_mul_log_two_le hk.le)).trans hka
  have hlk0 : 0 ≤ Real.log D.k := Real.log_nonneg hk1
  have hlk : Real.log D.k ≤ (1 + eK) * D.x ^ D.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hlH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
  have hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε :=
    log_one_add_rpow_le hx hHH hlog hy
  obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
  have hpow : D.x ^ (CErr C * D.ε)
      = D.x ^ (C.eDiv * D.ε) * D.x ^ (C.eLoss * D.ε) * D.x ^ D.ε * D.x ^ D.ε * D.x ^ D.ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    unfold CErr
    ring
  rw [hpow]
  unfold KBig at hbig
  have := core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := Real.log (Fintype.card (W u0) : ℝ)) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (y := D.x ^ D.ε) (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε)) (K := K)
    (h := 1 + C.cHH) (g := 1 + eK)
    hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
    hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
    (by linarith only [hHH]) (by linarith only [heK]) hbig
  unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
  exact this
end Formalism.LFunctionChainParameters.LChain
