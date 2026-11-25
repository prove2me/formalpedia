-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.map_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:21.982845+00:00
-- url     : https://prove2.me/submissions/c95fb4a6-f5e3-48fb-9f4e-71d028f63411

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_rkK_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_rkK_pos
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_nPl_pos
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_htQ_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_mu_eq
import Theorems.Thm_Formalism_HN_height_image_formula
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeIneq_rk
import Theorems.Thm_Formalism_HN_size_maximal_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : MapMu := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hA hB hA0 hinj hAB hrk
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxk⟩
    have hx0 : φ x = 0 := hxk
    exact (Submodule.mem_bot _).2 (hinj hxA A.zero_mem (by rw [hx0, map_zero]))
  have hrkI : rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A := by
    have h := sizeIneq_rk φ A
    rw [hker, ms_rkK_bot, add_zero] at h
    exact h
  obtain ⟨-, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hA
  rw [hker, ms_htQ_bot, hrkI] at hht
  set I := A.map (φ.restrictScalars (𝓞 K)) with hI
  have hIfg : I.FG := hA.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    have h0 := ms_rkK_pos b hA0
    rw [← hrkI, h, ms_rkK_bot] at h0
    exact lt_irrefl _ h0
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hAB))
  have hmono : ht b' X' B ≤ ht b' X' I :=
    (size_maximal_slope K W κ b' X' hX' I hIfg hI0).2.2.2.2.2 B hAB hB (hrk.trans hrkI.symm)
  obtain ⟨-, -, hposA⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨-, -, hposB⟩ := place_lattice_structure K W κ b' X' hX' B hB
  obtain ⟨-, -, hposI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hj : 0 < rkK A := ms_rkK_pos b hA0
  have hop : ∀ v, 0 < opNormAt b X b' X' v φ := by
    intro v
    have hnn : 0 ≤ opNormAt b X b' X' v φ := norm_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : (∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        rw [← h]
        exact zero_pow (by omega)
      rw [hz, zero_mul] at hht
      exact absurd hposI (not_lt.2 hht)
  have hlog : Real.log (ht b' X' B) ≤
      (rkK A : ℝ) * (∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)) + Real.log (ht b X A) := by
    have h1 : Real.log (ht b' X' B) ≤ Real.log ((∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) *
        ht b X A) := Real.log_le_log hposB (hmono.trans hht)
    have hpp : (∏ v, opNormAt b X b' X' v φ ^ (2 * rkK A)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hop v).ne'
    rw [Real.log_mul hpp hposA.ne', Real.log_prod (fun v _ => pow_ne_zero _ (hop v).ne')] at h1
    have h2 : (∑ v, Real.log (opNormAt b X b' X' v φ ^ (2 * rkK A))) =
        (rkK A : ℝ) * (∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    exact h1
  rw [ms_mu_eq b X hX hA hA0, ms_mu_eq b' X' hX' hB hB0, hrk]
  unfold htMap
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have hj' : (0 : ℝ) < rkK A := by exact_mod_cast hj
  set S := ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) with hS
  have key : (Real.log (ht b' X' B) - Real.log (ht b X A)) / ((nPl K : ℝ) * (rkK A : ℝ)) ≤
      1 / (nPl K : ℝ) * S := by
    rw [div_le_iff₀ (mul_pos hf hj')]
    have : 1 / (nPl K : ℝ) * S * ((nPl K : ℝ) * (rkK A : ℝ)) = (rkK A : ℝ) * S := by
      field_simp
    rw [this]
    linarith
  rw [sub_div] at key
  linarith
end Formalism.BranchingDeterminantCap
