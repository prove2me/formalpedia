-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pure_cross_term_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:13.764286+00:00
-- url     : https://prove2.me/submissions/0b59c7a9-023f-46a7-af45-f3881bd29a86

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_congr
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_CX
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pow_pair_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frob_iter
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_prod
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : PureCross.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hlt ι _ _ M hM be hbe0 hW hNB
  classical
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hlt.le
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := by
    intro x; simp [linSub]
  have hlinT : ∀ x i, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l)
      (MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun x i => wtGe_CX h0 (fun _ => rho l) i (hM x i)
  have hlin : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (linSub M x) := fun x =>
    wtGe_sum h0 Finset.univ _ fun i _ => hlinT x i
  have hsub : ∀ ab : Fin N0 × Fin N1,
      MvPowerSeries.HasSubst (fun s : ZMod d => linSub M (s, ab.1, ab.2)) :=
    fun ab => MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _
  have hp : ∀ (ab : Fin N0 × Fin N1) (n : ZMod d →₀ ℕ),
      WtGe ‖(l : K)‖ (fun _ : ι => rho l) (dot n (fun _ => rho l))
        (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) := by
    intro ab n
    have := wtGe_prod h0 n.support (fun s => (n s : ℝ) * rho l)
      (fun s => linSub M (s, ab.1, ab.2) ^ n s) fun s _ => wtGe_pow h0 (hlin _) (n s)
    simpa [dot, Finsupp.sum, Finsupp.prod] using this
  refine ⟨?_, ?_⟩
  · unfold bSum
    refine wtGe_sum h0 _ _ fun ab _ => ?_
    exact substitution_weight_bound K ‖(l : K)‖ h0 hlt (ZMod d) ι _ (fun _ => rho l) (fun _ => rho l) _ be
      (fun s => hlin0 _) (fun s => hlin _) hW
  · intro m hm
    rw [monoWtGe_iff]
    unfold bSum
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun ab _ => ?_
    rw [MvPowerSeries.coeff_subst (hsub ab)]
    refine norm_finsum_le_of (Real.rpow_nonneg h0.le _) fun n => ?_
    rw [smul_eq_mul, norm_mul]
    by_cases hn : IsBiPower l n
    · obtain ⟨s, s', α, β, -, -, -, -, rfl⟩ := hn
      have hprod : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)).prod
          (fun t e => linSub M (t, ab.1, ab.2) ^ e) =
          linSub M (s, ab.1, ab.2) ^ (l ^ α) * linSub M (s', ab.1, ab.2) ^ (l ^ β) := by
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      rw [hprod]
      set A := linSub M (s, ab.1, ab.2) with hA
      set B := linSub M (s', ab.1, ab.2) with hB
      set P := ∑ i, (MvPowerSeries.C (M (s, ab.1, ab.2) i) * MvPowerSeries.X i) ^ (l ^ α) with hP
      set P' := ∑ j, (MvPowerSeries.C (M (s', ab.1, ab.2) j) * MvPowerSeries.X j) ^ (l ^ β)
        with hP'
      have hEA : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ α : ℕ) : ℝ) * rho l + 1) (A ^ (l ^ α) - P) :=
        frob_iter hl h0 h1 Finset.univ _ (fun i _ => hlinT (s, ab.1, ab.2) i) α
      have hEB : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ β : ℕ) : ℝ) * rho l + 1) (B ^ (l ^ β) - P') :=
        frob_iter hl h0 h1 Finset.univ _ (fun i _ => hlinT (s', ab.1, ab.2) i) β
      have hPw : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ α : ℕ) : ℝ) * rho l) P :=
        wtGe_sum h0 _ _ fun i _ => wtGe_pow h0 (hlinT _ i) _
      have hBw : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ β : ℕ) : ℝ) * rho l) (B ^ (l ^ β)) :=
        wtGe_pow h0 (hlin _) _
      have hD : WtGe ‖(l : K)‖ (fun _ => rho l)
          ((((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l) + 1)
          (A ^ (l ^ α) * B ^ (l ^ β) - P * P') := by
        have e : A ^ (l ^ α) * B ^ (l ^ β) - P * P' =
            (A ^ (l ^ α) - P) * B ^ (l ^ β) + P * (B ^ (l ^ β) - P') := by ring
        rw [e]
        have := wtGe_add h0 h1 (wtGe_mul h0 hEA hBw) (wtGe_mul h0 hPw hEB)
        refine wtGe_congr ?_ this
        rw [show ((l ^ α : ℕ) : ℝ) * rho l + 1 + ((l ^ β : ℕ) : ℝ) * rho l =
            ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l + 1 by ring,
          show ((l ^ α : ℕ) : ℝ) * rho l + (((l ^ β : ℕ) : ℝ) * rho l + 1) =
            ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l + 1 by ring, min_self]
      have hPP : MvPowerSeries.coeff m (P * P') = 0 := by
        rw [hP, hP', Finset.sum_mul_sum, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [pow_pair_eq, MvPowerSeries.coeff_monomial_ne]
        exact fun h => hm ⟨i, j, α, β, h⟩
      have hcoef : MvPowerSeries.coeff m (A ^ (l ^ α) * B ^ (l ^ β)) =
          MvPowerSeries.coeff m (A ^ (l ^ α) * B ^ (l ^ β) - P * P') := by
        rw [map_sub, hPP, sub_zero]
      rw [hcoef]
      have hdn : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ => rho l) =
          ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l := by
        rw [dot_add, dot_single, dot_single]
      have hbn := hW (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      rw [monoWtGe_iff, hdn] at hbn
      calc _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - 1 -
              (((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l)) *
            ‖(l : K)‖ ^ ((((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l) + 1 -
              dot m (fun _ => rho l)) :=
          mul_le_mul hbn (hD m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
        _ = _ := by rw [← Real.rpow_add h0]; congr 1; ring
    · have hb := hNB n hn
      rw [monoWtGe_iff] at hb
      calc _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n (fun _ => rho l)) *
            ‖(l : K)‖ ^ (dot n (fun _ => rho l) - dot m (fun _ => rho l)) :=
          mul_le_mul hb (hp ab n m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
        _ = _ := by rw [← Real.rpow_add h0]; congr 1; ring
end Formalism.DworkPowerSeriesWeights
