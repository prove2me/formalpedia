-- Prove2me | solution 1 for Formalism.L2.Th1.D.dual_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:42.669741+00:00
-- url     : https://prove2.me/submissions/812b1197-50eb-4332-9b62-84e605f051ac

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_card_even
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sum_even
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_iter_sub_two
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_parity_sub_two


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open InverseCommuting
namespace Formalism.L2.Th1.D
theorem _root_.solution : DualExpand := by
  intro K _ d _ σ hd ι _ _ om oms hfix hT x hx
  obtain ⟨hcard, hdual⟩ := hT
  let E := {s : ZMod d // s.val % 2 = 0}
  let A : Matrix ι E K := fun r s => σ^[s.1.val] (om r)
  let B : Matrix E ι K := fun s r => σ^[s.1.val] (oms r)
  have hAB : A * B = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← hdual r r', sum_even]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (iterate_map_mul σ _ _ _).symm
  have hce : Fintype.card ι = Fintype.card E := by
    have h := card_even (d := d) hd
    show Fintype.card ι = Fintype.card {s : ZMod d // s.val % 2 = 0}
    omega
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hce)).1 hAB
  have hBA' : ∀ s s' : E, ∑ r, σ^[s.1.val] (oms r) * σ^[s'.1.val] (om r) =
      if s = s' then 1 else 0 := by
    intro s s'
    have := congrFun (congrFun hBA s) s'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  let z : E := ⟨0, by simp⟩
  have hz : ∀ y : K, σ^[z.1.val] y = y := by
    intro y
    have : z.1.val = 0 := ZMod.val_zero
    rw [this]
    rfl
  refine ⟨fun r r' => ?_, fun r => ?_, fun r' => ?_⟩
  · have hc : σ^[d] (x * oms r * om r') = x * oms r * om r' := by
      rw [iterate_map_mul, iterate_map_mul, hx, (hfix r).2, (hfix r').1]
    rw [map_sum, map_sum]
    rw [← (Equiv.subRight (2 : ZMod d)).sum_comp
      (fun s : ZMod d => σ (σ (if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0)))]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Equiv.subRight_apply]
    rw [KernelCokernelKilling.parity_sub_two hd s]
    split_ifs
    · exact KernelCokernelKilling.iter_sub_two σ hc s
    · simp
  · simp_rw [sum_even, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ s : E, ∑ r' : ι, σ^[s.1.val] (x * oms r * om r') * oms r' =
        σ^[s.1.val] (x * oms r) * if z = s then 1 else 0 := by
      intro s
      rw [← hBA' z s, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hz, iterate_map_mul σ _ (x * oms r)]
      ring
    simp_rw [this]
    simp [hz]
  · simp_rw [sum_even, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ s : E, ∑ r : ι, σ^[s.1.val] (x * oms r * om r') * om r =
        σ^[s.1.val] (x * om r') * if s = z then 1 else 0 := by
      intro s
      rw [← hBA' s z, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hz, iterate_map_mul, iterate_map_mul, iterate_map_mul]
      ring
    simp_rw [this]
    simp [hz]
end Formalism.L2.Th1.D
