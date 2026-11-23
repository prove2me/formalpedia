-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.generalized_log_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:21.431843+00:00
-- url     : https://prove2.me/submissions/66457830-a830-497c-880c-a36c97aff635

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_truncBelow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_X_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_IncomingBounds_padicValuationGain
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
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : GenLogWeight.{u, v} := by
  intro K _ _ _ l hl hπ τ _ _ p g hg0 hsub
  have hl2 := hl.two_le
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hg1 : ∀ z, Low 1 (g z) := fun z => (low_one_iff _).2 (hg0 z)
  suffices H : ∀ N, ∀ y, ∀ n : τ →₀ ℕ, n.degree = N →
      ‖coeff n (g y)‖ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) by
    intro x n
    rw [monoWtGe_iff, dot_const]
    exact H _ x n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro y n hn
  have hw : ∀ z, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (truncBelow N (g z)) := by
    intro z m
    rw [monoWtGe_iff, dot_const, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm z m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : ∀ z, Low N (g z - truncBelow N (g z)) := by
    intro z m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have htr1 : ∀ z, Low 1 (truncBelow N (g z)) := by
    intro z m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hg1 z m hm
    · rfl
  have hpow : ∀ z k, Low (N + k) (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1)) := by
    intro z k
    induction k with
    | zero => simpa using hlow z
    | succ k ihk =>
      have e : g z ^ (k + 1 + 1) - truncBelow N (g z) ^ (k + 1 + 1) =
          (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1)) * g z +
            truncBelow N (g z) ^ (k + 1) * (g z - truncBelow N (g z)) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk (hg1 z)))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow (htr1 z) (k + 1)) (hlow z)))
  have key := coeff_X_eq_sum hl2 p hg0 y (hsub y) n
  rw [Finset.sum_range_succ'] at key
  simp only [pow_zero, inv_one, one_mul, pow_one, Function.iterate_zero, id_eq] at key
  have hc : coeff n (g y) = coeff n (X y : MvPowerSeries τ K) + -∑ e ∈ Finset.range n.degree,
      ((l : K) ^ (e + 1))⁻¹ * coeff n (g (p^[e + 1] y) ^ ((l ^ 2) ^ (e + 1))) := by
    rw [key]; ring
  rw [hc]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_X]
    split_ifs with h
    · subst h
      simp [Finsupp.degree_single]
    · simpa using Real.rpow_nonneg hπ0.le _
  · rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hπ0.le _)
      fun e _ => ?_
    set k := (l ^ 2) ^ (e + 1) with hk
    have hk2 : 2 ≤ k := le_trans (by nlinarith) (Nat.le_self_pow (by omega) (l ^ 2))
    have hce : coeff n (g (p^[e + 1] y) ^ k) = coeff n (truncBelow N (g (p^[e + 1] y)) ^ k) := by
      have := hpow (p^[e + 1] y) (k - 1) n (by omega)
      rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
      exact this
    rw [hce, norm_mul, norm_inv, norm_pow]
    have hb := wtGe_pow hπ0 (hw (p^[e + 1] y)) k n
    rw [monoWtGe_iff, dot_const] at hb
    have hv := (padicValuationGain l hl).2 (e + 1)
    have hkr : ((k : ℕ) : ℝ) = ((l : ℝ) ^ 2) ^ (e + 1) := by rw [hk]; push_cast; ring
    calc (‖(l : K)‖ ^ (e + 1))⁻¹ * ‖coeff n (truncBelow N (g (p^[e + 1] y)) ^ k)‖
        ≤ (‖(l : K)‖ ^ (e + 1))⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * rho l - (n.degree : ℝ) * rho l) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (pow_nonneg hπ0.le _))
      _ = ‖(l : K)‖ ^ ((k : ℝ) * rho l - (n.degree : ℝ) * rho l - ((e + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_sub hπ0 ((k : ℝ) * rho l - (n.degree : ℝ) * rho l) ((e + 1 : ℕ) : ℝ),
            Real.rpow_natCast, div_eq_inv_mul]
      _ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) := by
          apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
          rw [hkr]
          push_cast at hv ⊢
          linarith
end Formalism.DworkPowerSeriesWeights
