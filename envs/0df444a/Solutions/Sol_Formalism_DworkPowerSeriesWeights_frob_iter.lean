-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frob_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:09.782984+00:00
-- url     : https://prove2.me/submissions/a50be792-2193-414d-88d0-43c4c4c0c34e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_congr
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frob_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mono
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum


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
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) (hpi1 : ‖(l : K)‖ ≤ 1)
    {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α) (A : α → MvPowerSeries ι K)
    (hA : ∀ i ∈ s, WtGe ‖(l : K)‖ r wt (A i)) (k : ℕ) :
    WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt + 1)
      ((∑ i ∈ s, A i) ^ (l ^ k) - ∑ i ∈ s, A i ^ (l ^ k)) := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, sub_self]
    exact wtGe_zero hpi0 r _
  | succ k ih =>
    set P := ∑ i ∈ s, A i ^ (l ^ k) with hP
    set E := (∑ i ∈ s, A i) ^ (l ^ k) - P with hE
    have hPw : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) P :=
      wtGe_sum hpi0 s _ fun i hi => wtGe_pow hpi0 (hA i hi) (l ^ k)
    have hEw' : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) E :=
      wtGe_mono hpi0 hpi1 (by linarith) ih
    have hPE : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) (P + E) := by
      have := wtGe_add hpi0 hpi1 hPw hEw'; rwa [min_self] at this
    have hG : WtGe ‖(l : K)‖ r (((l - 1 : ℕ) : ℝ) * (((l ^ k : ℕ) : ℝ) * wt))
        (∑ i ∈ Finset.range l, (P + E) ^ i * P ^ (l - 1 - i)) := by
      refine wtGe_sum hpi0 _ _ fun i hi => ?_
      have hi' : i ≤ l - 1 := by rw [Finset.mem_range] at hi; omega
      refine wtGe_congr ?_ (wtGe_mul hpi0 (wtGe_pow hpi0 hPE i) (wtGe_pow hpi0 hPw (l - 1 - i)))
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hi']
    have h1 : WtGe ‖(l : K)‖ r (((l ^ (k + 1) : ℕ) : ℝ) * wt + 1) ((P + E) ^ l - P ^ l) := by
      rw [← geom_sum₂_mul, show P + E - P = E by abel]
      refine wtGe_congr ?_ (wtGe_mul hpi0 hG ih)
      have hl1 : 1 ≤ l := hl.one_lt.le
      rw [Nat.cast_sub hl1]; push_cast; ring
    have h2 : WtGe ‖(l : K)‖ r (((l ^ (k + 1) : ℕ) : ℝ) * wt + 1)
        (P ^ l - ∑ i ∈ s, A i ^ (l ^ (k + 1))) := by
      have := frob_sum hl hpi0 hpi1 s (fun i => A i ^ (l ^ k))
        fun i hi => wtGe_pow hpi0 (hA i hi) (l ^ k)
      simp only [← pow_mul, ← pow_succ] at this
      refine wtGe_congr ?_ this
      push_cast; ring
    have h3 := wtGe_add hpi0 hpi1 h1 h2
    rw [min_self] at h3
    have e : (∑ i ∈ s, A i) ^ l ^ (k + 1) = (P + E) ^ l := by
      rw [pow_succ, pow_mul, hE]; congr 1; abel
    rw [e]; convert h3 using 1; abel
end Formalism.DworkPowerSeriesWeights
