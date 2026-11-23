-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.meanExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:07.939624+00:00
-- url     : https://prove2.me/submissions/93ce025f-1829-4f26-99d1-3dd414093ca9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_exists_mean
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_exists_far
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_exists_T_of_mem

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
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution : MeanExists := by
  intro f La _ _
  let b := Module.Free.chooseBasis ℤ La
  let Λ := La.toAddSubgroup
  let e : Module.Free.ChooseBasisIndex ℤ La → Λ := fun i => ⟨(b i : V f), (b i).2⟩
  set β : ℝ := ∑ i, ‖(b i : V f)‖ with hβ
  have hβ0 : 0 ≤ β := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hfar := fun n : ℕ => exists_far La ((n : ℝ) + (n + 1) * β)
  choose y hyLa hy using hfar
  let c : ℕ → Λ := fun n => ⟨y n, hyLa n⟩
  have he : AddSubgroup.closure (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    suffices hall : ∀ zL : La, (⟨zL.1, zL.2⟩ : Λ) ∈ AddSubgroup.closure (Set.range e) from
      hall ⟨z.1, z.2⟩
    intro zL
    have hxs : zL ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    induction hxs using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
    | zero => exact (AddSubgroup.closure (Set.range e)).zero_mem
    | add z1 z2 _ _ h1 h2 =>
      have := (AddSubgroup.closure (Set.range e)).add_mem h1 h2
      convert this using 1
      apply Subtype.ext
      simp
    | smul a z _ h =>
      have := (AddSubgroup.closure (Set.range e)).zsmul_mem h a
      convert this using 1
      apply Subtype.ext
      simp
  obtain ⟨hmean, hvan⟩ := exists_mean e he c
  refine ⟨LIMf e c, hmean, ?_⟩
  intro g hg htend
  apply hvan g hg
  intro ε hε
  have h1 : g ⁻¹' Metric.closedBall 0 ε ∈ Filter.comap (fun x : Λ => (x : V f)) (atInfAll f) :=
    htend (Metric.closedBall_mem_nhds 0 hε)
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp h1
  obtain ⟨T, hT⟩ := exists_T_of_mem ht
  filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn m hm
  have hmem : (bpt e (c n) m : Λ) ∈ (fun x : Λ => (x : V f)) ⁻¹' t := by
    apply hT
    intro v
    show T ≤ ‖((bpt e (c n) m : Λ) : V f) v‖
    have hcoe : ((bpt e (c n) m : Λ) : V f) = y n + ∑ i, m i • (b i : V f) := by
      simp [bpt, c, e]
    rw [hcoe, Pi.add_apply]
    have hs : ‖(∑ i, m i • (b i : V f)) v‖ ≤ (n + 1) * β := by
      calc ‖(∑ i, m i • (b i : V f)) v‖ ≤ ‖∑ i, m i • (b i : V f)‖ := norm_le_pi_norm _ v
        _ ≤ ∑ i, ‖m i • (b i : V f)‖ := norm_sum_le _ _
        _ ≤ ∑ i, (m i : ℝ) * ‖(b i : V f)‖ := Finset.sum_le_sum (fun i _ => norm_nsmul_le)
        _ ≤ ∑ i, ((n : ℝ) + 1) * ‖(b i : V f)‖ := by
            apply Finset.sum_le_sum
            intro i _
            have := Fintype.mem_piFinset.mp hm i
            simp only [Finset.mem_range] at this
            have : (m i : ℝ) ≤ n + 1 := by exact_mod_cast this.le
            gcongr
        _ = (n + 1) * β := by rw [hβ, Finset.mul_sum]
    have hyv := hy n v
    have htri := norm_sub_le (y n v + (∑ i, m i • (b i : V f)) v) ((∑ i, m i • (b i : V f)) v)
    rw [add_sub_cancel_right] at htri
    have hnT : T ≤ (n : ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast hn)
    linarith
  have := hts hmem
  simpa using this
end Formalism.FourierDecayAlt.P.BoxAverageLimits
