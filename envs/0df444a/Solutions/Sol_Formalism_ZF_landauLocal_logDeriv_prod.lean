-- Prove2me | solution 1 for Formalism.ZF.landauLocal_logDeriv_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:21.480812+00:00
-- url     : https://prove2.me/submissions/76ecdb58-b17d-464c-a0d2-d0b293672bfd

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology Metric
noncomputable section
namespace Formalism.ZF
private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv
private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring
end Formalism.ZF
end
end

set_option autoImplicit false
open Complex Filter Topology Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_apply, (hasDerivAt_prod_sub_pow Z m z hz).deriv]
  have hP : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hz ρ hρ)
  exact (div_eq_iff hP).mpr (mul_comm _ _)
end Formalism.ZF
