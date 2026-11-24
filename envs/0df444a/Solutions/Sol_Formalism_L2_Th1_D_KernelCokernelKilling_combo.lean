-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.combo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:47.186483+00:00
-- url     : https://prove2.me/submissions/1914ba21-2c71-4658-a792-41d536058211

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_parity_sub_two
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_iter_sub_two
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_norm_iter
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [NormedField K] {τ : Type}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution [IsUltrametricDist K] {l d : ℕ} [NeZero d] (hl : l ≠ 0) (σ : K →+* K)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) (hd : Even d) (L : ZMod d → MvPowerSeries τ K)
    (hL : ShiftType l σ L) {c : K} (hc : ‖c‖ ≤ 1) (hcd : σ^[d] c = c)
    (P : ℕ → Prop) [DecidablePred P] :
    IP l σ (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ZMod d → K, a = fun s => if P (s.val % 2) then σ^[s.val] c else 0 :=
    ⟨_, rfl⟩
  have hsum : (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) =
      ∑ s, C (a s) * L s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : P (s.val % 2) <;> simp [ha, h]
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl
  have hshift : ∀ s, (σ.comp σ) (a (s - 2)) = a s := by
    intro s
    simp only [ha, parity_sub_two hd s]
    split_ifs
    · rw [RingHom.comp_apply]
      exact iter_sub_two σ hcd s
    · exact map_zero _
  have hle : ∀ s, ‖a s‖ ≤ 1 := by
    intro s
    simp only [ha]
    split_ifs
    · exact norm_iter hσ hc _
    · simp
  rw [hsum]
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [map_mul, (hL s).1, mul_zero]
  · have key : (∑ s, C (a s) * L s) - C ((l : K)⁻¹) *
          frobVar (l ^ 2) (map (σ.comp σ) (∑ s, C (a s) * L s)) =
        ∑ s, C (a s) * (L s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (L (s - 2)))) := by
      simp only [Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hq, map_sum, map_mul, MvPowerSeries.map_C,
        MvPowerSeries.expand_C, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← (Equiv.subRight (2 : ZMod d)).sum_comp]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Equiv.subRight_apply, hshift]
      ring
    intro n
    rw [key, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [coeff_C_mul, norm_mul]
    exact mul_le_one₀ (hle s) (norm_nonneg _) ((hL s).2 n)
end Formalism.L2.Th1.D.KernelCokernelKilling
