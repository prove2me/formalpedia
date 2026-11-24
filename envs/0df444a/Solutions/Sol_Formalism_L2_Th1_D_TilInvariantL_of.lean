-- Prove2me | solution 1 for Formalism.L2.Th1.D.TilInvariantL_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:21.933874+00:00
-- url     : https://prove2.me/submissions/b2dcf679-45bc-4006-8654-a96caae89100

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_symm
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_trans
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_sum
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sum_rule
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_linEL_sum
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_linOL_sum
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_norm_iter


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open InverseCommuting
namespace Formalism.L2.Th1.D
theorem _root_.solution : PairRules → SubstTil → TorusTil → TeichSigma → ShiftIP → IPClosure →
    DualExpand → FrobSq → TilInvariantL := by
  intro hPR hST hTT hTS hSI hIC hDE hFS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms
    hOw hT u hu τ _ L hL
  have hl2 : 2 ≤ l := hU.1.two_le
  have hσ := (hFS K l σ hU).2
  have h1 : 1 < l ^ d := Nat.one_lt_pow (by omega) hU.1.one_lt
  have hN : l ^ d - 1 ≠ 0 := by omega
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow hN] at hu
    exact zero_ne_one hu
  have hnu : ‖u‖ = 1 := by
    have h : ‖u‖ ^ (l ^ d - 1) = 1 := by rw [← norm_pow, hu, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) hN).1 h
  have hσu : σ u = u ^ l := hTS K l d σ hU (by omega) u hu
  have hiter : ∀ k, σ^[k] u = u ^ (l ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_pow, hσu, ← pow_mul, pow_succ']
  have hud : σ^[d] u = u := by
    have e : l ^ d = (l ^ d - 1) + 1 := by omega
    rw [hiter, e, pow_succ, hu, one_mul]
  have hui : σ^[d] u⁻¹ = u⁻¹ := by
    rw [← RingHom.coe_pow, map_inv₀, RingHom.coe_pow, hud]
  have hnui : ‖u⁻¹‖ = 1 := by rw [norm_inv, hnu, inv_one]
  obtain ⟨hPR1, hPR2, hPR3⟩ := hPR K l σ hU F hF be0 hF1 τ
  have hPR3 := hPR3 hF2
  obtain ⟨hI0, hIadd, hImul⟩ := hIC K l σ τ
  obtain ⟨hc1, hc2, hc3⟩ := hDE K d σ hd ι om oms hOw.2 hT u hud
  obtain ⟨c, hcn, hc1, hc2, hc3⟩ : ∃ c : ι → ι → K, (∀ r r', ‖c r r'‖ ≤ 1) ∧
      (∀ r r', σ (σ (c r r')) = c r r') ∧ (∀ r, u * oms r = ∑ r', c r r' * oms r') ∧
      (∀ r', u * om r' = ∑ r, c r r' * om r) := by
    refine ⟨fun r r' => ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (u * oms r * om r') else 0,
      ?_, hc1, hc2, hc3⟩
    intro r r'
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    split_ifs
    · refine KernelCokernelKilling.norm_iter hσ ?_ _
      rw [norm_mul, norm_mul, hnu, one_mul]
      exact mul_le_one₀ (hOw.1 r).2 (norm_nonneg _) (hOw.1 r').1
    · simp
  have hA : ∀ r, IP l σ (linEL σ (oms r) L) := fun r =>
    (hSI K l d σ hU hd τ L hL (oms r) (hOw.1 r).2 (hOw.2 r).2).1
  have hBu : ∀ r, IP l σ (linOL σ (u⁻¹ * om r) L) := fun r =>
    (hSI K l d σ hU hd τ L hL (u⁻¹ * om r)
      (by rw [norm_mul, hnui, one_mul]; exact (hOw.1 r).1)
      (by rw [iterate_map_mul, hui, (hOw.2 r).1])).2
  have hAu : ∀ r, linEL σ (u * oms r) L = ∑ r', C (c r r') * linEL σ (oms r') L := by
    intro r
    rw [hc2 r, linEL_sum σ _ _ (hc1 r) L]
  have hB : ∀ r', linOL σ (om r') L = ∑ r, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L := by
    intro r'
    rw [← linOL_sum σ (fun r => c r r') (fun r => u⁻¹ * om r) (fun r => hc1 r r') L]
    congr 1
    have e : ∑ r, c r r' * (u⁻¹ * om r) = u⁻¹ * ∑ r, c r r' * om r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, ← hc3 r', inv_mul_cancel_left₀ hu0]
  have hL0 : ∀ s, constantCoeff (L s) = 0 := fun s => (hL s).1
  rw [hTT K l d σ hl2 be0 ι om oms u hu0 hσu, hST K l d σ hl2 be0 ι _ _ τ L hL0,
    hST K l d σ hl2 be0 ι om oms τ L hL0]
  show Simeq (∑ r, subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0))
    (∑ r, subst ![linEL σ (oms r) L, linOL σ (om r) L] (addC l be0))
  have s1 : ∀ r, Simeq (subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0))
      (∑ r', subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0)) := by
    intro r
    rw [hAu r]
    exact (sum_rule hI0 hIadd (fun G => subst ![G, linOL σ (u⁻¹ * om r) L] (addC l be0))
      (fun g g' hg hg' => hPR1 g g' _ hg hg' (hBu r)) Finset.univ _
      (fun r' _ => hImul _ _ (hcn r r') (hc1 r r') (hA r'))).2
  have s2 : ∀ r r',
      Simeq (subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0))
        (subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L] (addC l be0)) :=
    fun r r' => hPR3 _ _ _ (hcn r r') (hc1 r r') (hA r') (hBu r)
  have s3 : ∀ r', Simeq (subst ![linEL σ (oms r') L, linOL σ (om r') L] (addC l be0))
      (∑ r, subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L]
        (addC l be0)) := by
    intro r'
    rw [hB r']
    exact (sum_rule hI0 hIadd (fun H => subst ![linEL σ (oms r') L, H] (addC l be0))
      (fun g g' hg hg' => hPR2 _ g g' (hA r') hg hg') Finset.univ _
      (fun r _ => hImul _ _ (hσ _ (hcn r r')) (by rw [hc1]) (hBu r))).2
  refine sim_trans (sim_sum _ _ _ fun r _ => s1 r) ?_
  refine sim_trans (sim_sum _ _ _ fun r _ => sim_sum _ _ _ fun r' _ => s2 r r') ?_
  rw [Finset.sum_comm]
  exact sim_symm (sim_sum _ _ _ fun r' _ => s3 r')
end Formalism.L2.Th1.D
