-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.leakage_share_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:00.949317+00:00
-- url     : https://prove2.me/submissions/e0c43e4c-a737-4c33-b2c2-e75eb755c4ed

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_half
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_sum_cond_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_y_facts
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_q
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : LeakShare := by
  refine ⟨3, ?_⟩
  intro U T _ _ _ _ Q cond q a ρ j hq hρ hT hcnt hS
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set g : ℕ → ℝ := fun i => ((q : ℝ) ^ ((i - j) * ρ))⁻¹ with hg
  obtain ⟨N, hN⟩ := sum_cond_le cond g (fun i => (q : ℝ) ^ i * g i) (fun i => by
    have : 0 ≤ g i := by simp only [hg]; positivity
    exact mul_le_mul_of_nonneg_right (hcnt i) this)
  have hsumB : ∑ i ∈ range (j + 1 + N), (q : ℝ) ^ i * g i ≤ 3 * (q : ℝ) ^ j := by
    rw [Finset.sum_range_add]
    have h1 : ∑ i ∈ range (j + 1), (q : ℝ) ^ i * g i = ∑ i ∈ range (j + 1), (q : ℝ) ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i - j = 0 := by have := Finset.mem_range.1 hi; omega
      simp [hg, this]
    have h2 : ∑ l ∈ range N, (q : ℝ) ^ (j + 1 + l) * g (j + 1 + l) = (q : ℝ) ^ j * (y * ∑ l ∈ range N, y ^ l) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : j + 1 + l - j = l + 1 := by omega
      simp only [hg, this]
      rw [hy, ← pow_succ', mul_pow, inv_pow, ← pow_mul, mul_comm ρ (l + 1)]
      ring
    rw [h1, h2]
    have h3 := geo_q q hq2 j
    have h4 := geo_half y hy0 (by linarith) N
    have h5 : 0 ≤ y ^ N := pow_nonneg hy0 _
    have h6 : y * ∑ l ∈ range N, y ^ l ≤ 1 := by nlinarith
    have h7 : 0 < (q : ℝ) ^ j := by positivity
    nlinarith
  have h0 := orth_sum Q (fun _ => (1 : ℂ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h0
  have h1 : ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a ≤ 3 * (q : ℝ) ^ j * (Fintype.card U : ℝ) := by
    have : ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a
        = ‖((univ.filter fun u => Q u = 0).card : ℂ) * (Fintype.card T : ℂ)‖ := by
      rw [hT]; simp
    rw [this, h0]
    calc _ ≤ ∑ ψ : AddChar T ℂ, ‖∑ u, ψ (Q u)‖ := norm_sum_le _ _
      _ ≤ ∑ ψ : AddChar T ℂ, g (cond ψ) * (Fintype.card U : ℝ) := Finset.sum_le_sum fun ψ _ => hS ψ
      _ = (∑ ψ : AddChar T ℂ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          exact (hN (j + 1 + N) (by omega)).trans hsumB
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact h1
end Formalism.HermitianLatticeCounting.P.S4aux
