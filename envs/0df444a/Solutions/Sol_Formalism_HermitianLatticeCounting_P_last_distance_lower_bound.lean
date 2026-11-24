-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.last_distance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:38.223904+00:00
-- url     : https://prove2.me/submissions/9a3de5a5-7024-44d2-9554-9172dfd36281

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_majorant_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := by
  intro V _ _ θ h r y T hG
  unfold majorantHermitianForm at hG
  set W : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < Fin.last r}) with hW

  have s1 : ∀ b, ∀ w ∈ W, inner ℂ (θ (y b)) w = 0 := by
    intro b w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have := hG a b
      rw [this, if_neg]
      rintro ⟨h1, -⟩
      exact (ne_of_lt ha) h1
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have s2 : ∀ b, ∀ w ∈ W, inner ℂ (θ w) (y b) = 0 := by
    intro b w hw
    rw [h.2, ← inner_conj_symm, s1 b w hw, map_zero]
  have s3 : ∀ w ∈ W, ∀ w' ∈ W, inner ℂ (θ w) w' = 0 := by
    intro w hw w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact s2 a w hw
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have key : ∀ w ∈ W, T ≤ ‖y (Fin.last r) - w‖ ^ 2 := by
    intro w hw
    have e : inner ℂ (θ (y (Fin.last r) - w)) (y (Fin.last r) - w) = -(T : ℂ) := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, s1 _ w hw, s2 _ w hw, s3 w hw w hw,
        hG, if_pos ⟨rfl, rfl⟩]
      ring
    have m := gram_majorant_bound V θ h (y (Fin.last r) - w)
    unfold majorantHermitianForm at m
    rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs] at m
    exact (le_abs_self T).trans m
  unfold majorantDistance
  rcases le_or_gt T 0 with hT | hT
  · exact hT.trans (sq_nonneg _)
  · have hne : ((W : Set V)).Nonempty := ⟨0, W.zero_mem⟩
    have : √T ≤ Metric.infDist (y (Fin.last r)) (W : Set V) := by
      rw [Metric.le_infDist hne]
      intro w hw
      rw [dist_eq_norm]
      exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, key w hw⟩
    calc T = √T ^ 2 := (Real.sq_sqrt hT.le).symm
      _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
