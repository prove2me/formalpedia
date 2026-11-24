-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.tendsto_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.862047+00:00
-- url     : https://prove2.me/submissions/7a7cb825-f2c1-419b-b1d8-70c6e8a6ae83

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_dif_eq_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_eq_tsum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_dif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (hRS : ∀ i ∈ S, ∀ j, R i j = 1)
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c C : ℝ)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v) :
    Tendsto (fun j => sc j * ∑ n ∈ B j, a n * (val n).prod R) atTop
      (𝓝 (c * ∑' v : ι →₀ ℕ, v.prod (dif R) / nrm q v)) := by
  have hlim : Tendsto (fun j => ∑' v : ι →₀ ℕ,
      v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n)) atTop
      (𝓝 (∑' v : ι →₀ ℕ, v.prod (dif R) * (c / nrm q v))) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun j v => v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n))
      (g := fun v => v.prod (dif R) * (c / nrm q v))
      (bound := fun v => C * (|v.prod (dif R)| / nrm q v))
      ((summable_dif hq hsum hRb).mul_left C) ?_ ?_
    · intro v
      try dsimp only
      by_cases hv : Disjoint v.support S
      · exact (H1 v hv).const_mul _
      · obtain ⟨i, hiv, hiS⟩ := Finset.not_disjoint_iff.mp hv
        have h0 : v.prod (dif R) = 0 := prod_dif_eq_zero hiv (hRS i hiS)
        simp only [h0, zero_mul]
        exact tendsto_const_nhds
    · filter_upwards [H2] with j hj v
      try dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      calc |v.prod (dif R)| * |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n|
          ≤ |v.prod (dif R)| * (C / nrm q v) :=
            mul_le_mul_of_nonneg_left (hj v) (abs_nonneg _)
        _ = C * (|v.prod (dif R)| / nrm q v) := by ring
  have heq : ∀ j, ∑' v : ι →₀ ℕ,
      v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) =
        sc j * ∑ n ∈ B j, a n * (val n).prod R :=
    fun j => (sum_eq_tsum hR0 val (B j) a (sc j)).symm
  have hcl : ∑' v : ι →₀ ℕ, v.prod (dif R) * (c / nrm q v) =
      c * ∑' v : ι →₀ ℕ, v.prod (dif R) / nrm q v := by
    rw [← tsum_mul_left]
    refine tsum_congr fun v => ?_
    ring
  rw [← hcl]
  exact Tendsto.congr heq hlim
end Formalism.HermitianLattices.Ext.L3.A5
