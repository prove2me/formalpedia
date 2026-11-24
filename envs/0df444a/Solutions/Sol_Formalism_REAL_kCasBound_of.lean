-- Prove2me | solution 1 for Formalism.REAL.kCasBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:34.252801+00:00
-- url     : https://prove2.me/submissions/1424b3e3-3418-424e-8d65-98026fd9a57e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_compactCasimirValue_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hd : KDecomp) (hc : KCasSpan) (ho : KOrth) : KCasBound := by
  intro V _ _ n ε F S R hfin hr hu hS hR hw y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => hc V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact compactCasimirValue_le ε (μ i) R (hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2.1)
end Formalism.REAL
