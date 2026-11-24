-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.sum_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:39.618676+00:00
-- url     : https://prove2.me/submissions/676d7dd7-57cb-46e0-8801-ff2bd11429a5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_ebox_support
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_eq_sum_dif


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
theorem _root_.solution {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (val : X → ι →₀ ℕ) (B : Finset X)
    (a : X → ℝ) (sc : ℝ) :
    sc * ∑ n ∈ B, a n * (val n).prod R =
      ∑' v : ι →₀ ℕ, v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) := by
  set T : Finset (ι →₀ ℕ) := B.biUnion fun n => ebox (val n).support (val n) with hT
  have hfil : ∀ n ∈ B, T.filter (fun v => v ≤ val n) = ebox (val n).support (val n) := by
    intro n hn
    ext v
    rw [Finset.mem_filter, mem_ebox_support]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_biUnion.mpr ⟨n, hn, mem_ebox_support.mpr h⟩, h⟩
  have hzero : ∀ v ∉ T,
      v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) = 0 := by
    intro v hv
    have hE : B.filter (fun n => v ≤ val n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn hle
      exact hv (Finset.mem_biUnion.mpr ⟨n, hn, mem_ebox_support.mpr hle⟩)
    rw [hE, Finset.sum_empty, mul_zero, mul_zero]
  have lhs : sc * ∑ n ∈ B, a n * (val n).prod R =
      ∑ v ∈ T, ∑ n ∈ B, if v ≤ val n then v.prod (dif R) * (sc * a n) else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [prod_eq_sum_dif R hR0 (val n), ← hfil n hn, Finset.sum_filter, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  have rhs : ∀ v : ι →₀ ℕ,
      v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) =
        ∑ n ∈ B, if v ≤ val n then v.prod (dif R) * (sc * a n) else 0 := by
    intro v
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [lhs, (hasSum_sum_of_ne_finset_zero hzero).tsum_eq]
  exact Finset.sum_congr rfl fun v _ => (rhs v).symm
end Formalism.HermitianLattices.Ext.L3.A5
