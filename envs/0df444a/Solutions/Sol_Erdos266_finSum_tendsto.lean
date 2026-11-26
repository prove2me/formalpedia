-- Prove2me | solution 1 for Erdos266.finSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:46.629083+00:00
-- url     : https://prove2.me/submissions/93611c3d-6649-459c-b842-2ec643d5ec42

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_inv_inf
public import Theorems.Thm_Erdos266_radius_le
public import Theorems.Thm_Erdos266_bigN_tendsto
public import Theorems.Thm_Erdos266_tailAnchor_nonneg
public import Theorems.Thm_Erdos266_le_dOf
public import Theorems.Thm_Erdos266_succ_le_two_pow
public import Theorems.Thm_Erdos266_tailAnchor_tendsto
public import Theorems.Thm_Erdos266_two_le_mseq


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (i' : ℕ) :
    Tendsto (fun k => finSum i' k Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound : ∀ᶠ k in atTop, ‖finSum i' k Sinf - ((xinf i' : ℚ) : ℝ)‖
      ≤ ((bigN k : ℝ))⁻¹ + tailAnchor (i' + 1) k := by
    rw [eventually_atTop]
    refine ⟨max (mseq (i' + 1)) (2 * i' + 2), fun k hk => ?_⟩
    have hk1 : mseq (i' + 1) ≤ k := le_trans (le_max_left _ _) hk
    have hk2 : 2 ≤ k := le_trans (two_le_mseq _) hk1
    have hdk : i' < dOf k := lt_of_lt_of_le (Nat.lt_succ_self i') (le_dOf hk1)
    have h2i : 2 * (i' + 1) ≤ bigN k := by
      have h3 : k + 1 ≤ bigN k := by
        have h4 := succ_le_two_pow k
        have h5 : (2:ℕ) ^ k ≤ bigN k := by
          rw [bigN]
          exact Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by norm_num) k)
        omega
      have h6 : 2 * i' + 2 ≤ k := le_trans (le_max_right _ _) hk
      omega
    have htail0 : 0 ≤ tailAnchor (i' + 1) k := tailAnchor_nonneg h2i
    have hinv := inv_inf hk2 hdk
    rw [Real.norm_eq_abs]
    calc |finSum i' k Sinf - ((xinf i' : ℚ) : ℝ)|
        = |(finSum i' k Sinf + tailAnchor (i' + 1) k - ((xinf i' : ℚ) : ℝ))
            + (-(tailAnchor (i' + 1) k))| := by
          congr 1
          ring
    _ ≤ |finSum i' k Sinf + tailAnchor (i' + 1) k - ((xinf i' : ℚ) : ℝ)|
          + |(-(tailAnchor (i' + 1) k))| := abs_add_le _ _
    _ ≤ ((bigN k : ℝ))⁻¹ + tailAnchor (i' + 1) k := by
          refine add_le_add (hinv.trans (radius_le hk2)) ?_
          rw [abs_neg, abs_of_nonneg htail0]
  refine squeeze_zero_norm' hbound ?_
  have h1 : Tendsto (fun k => ((bigN k : ℝ))⁻¹) atTop (𝓝 0) :=
    bigN_tendsto.inv_tendsto_atTop
  have h2 := tailAnchor_tendsto (i' + 1)
  simpa using h1.add h2
end Erdos266
