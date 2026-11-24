-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.gauss_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:34.102159+00:00
-- url     : https://prove2.me/submissions/02f0a4e0-7c3a-4a22-8c1b-5f1988d936ba

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_half
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_sum_cond_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_y_facts
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
theorem _root_.solution {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ)
    (hq : 2 ≤ q) (hρ : 4 ≤ ρ) (hT : Fintype.card T = q ^ a)
    (hc0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0)
    (hcnt : ∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i)
    (hS : ∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * f u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) :
    ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)‖
      ≤ 2 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) := by
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  have hq0 : (0 : ℝ) < q := by positivity
  set g : ℕ → ℝ := fun i => if i = 0 then 0 else ((q : ℝ) ^ (i * ρ))⁻¹ with hg
  set B : ℕ → ℝ := fun i => if i = 0 then 0 else y ^ i with hB
  have hgB : ∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) * g i ≤ B i := by
    intro i
    by_cases hi : i = 0
    · simp [hg, hB, hi]
    · simp only [hg, hB, if_neg hi]
      have : y ^ i = (q : ℝ) ^ i * ((q : ℝ) ^ (i * ρ))⁻¹ := by
        rw [hy, mul_pow, inv_pow, ← pow_mul, mul_comm ρ i]
      rw [this]
      gcongr
      exact hcnt i (Nat.one_le_iff_ne_zero.2 hi)
  obtain ⟨N, hN⟩ := sum_cond_le cond g B hgB
  have hsumB : ∑ i ∈ range (N + 1), B i ≤ 2 * y := by
    rw [Finset.sum_range_succ']
    simp only [hB, if_true, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    have := geo_half y hy0 (by linarith) N
    have h2 : ∑ k ∈ range N, y ^ (k + 1) = y * ∑ k ∈ range N, y ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2]
    have h3 : 0 ≤ y ^ N := pow_nonneg hy0 _
    nlinarith
  have hmain : ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u‖
      ≤ 2 * y * (Fintype.card U : ℝ) := by
    have h0 := orth_sum Q f
    rw [hT, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar T ℂ))] at h0
    simp only [AddChar.zero_apply, one_mul] at h0
    push_cast at h0
    rw [h0, add_sub_cancel_left]
    calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), ‖∑ u, ψ (Q u) * f u‖ := norm_sum_le _ _
      _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum fun ψ hψ => ?_
          have hψ0 : ψ ≠ 0 := (Finset.mem_erase.1 hψ).1
          have : cond ψ ≠ 0 := fun h => hψ0 ((hc0 ψ).1 h)
          simp only [hg, if_neg this]
          exact hS ψ hψ0
      _ ≤ ∑ ψ, g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun ψ _ _ => ?_
          simp only [hg]; split_ifs <;> positivity
      _ = (∑ ψ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          exact (hN (N + 1) (by omega)).trans hsumB
  have hqa : ((q : ℂ) ^ a) ≠ 0 := by
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    exact pow_ne_zero _ this
  have hnq : ‖((q : ℂ) ^ a)‖ = (q : ℝ) ^ a := by simp
  have : (∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)
      = ((∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u) / ((q : ℂ) ^ a) := by
    field_simp
  rw [this, norm_div, hnq, ← mul_div_assoc]
  gcongr
end Formalism.HermitianLatticeCounting.P.S4aux
