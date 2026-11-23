-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.shiftBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:58.064067+00:00
-- url     : https://prove2.me/submissions/ef279992-b187-48e4-bc4d-a1ddd1aad5a9

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_th_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_shift_pt
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_gs_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution : ShiftBound := by
  intro B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hW hP hI4' h5 hRes hWR hPR hb Y s hY hYs
  have hint : Integrable (fun ω => th ε σ (B.G ω) * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) B.μ := by
    have := (hI4' ε hε).1 (Y + s) hYs 0
    rwa [gs_zero] at this
  have h1 : S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := by
    unfold Step.Ens Step.En
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 Y hY ω a).le (by positivity))))
    · exact hint.const_mul _
    · exact Filter.Eventually.of_forall (fun ω => by
        have := mul_le_mul_of_nonneg_left (shift_pt S CR Cd hCR hCd hW h5 hRes hWR Y s hY hYs ω) (th_nonneg B ε σ hε ω)
        simp only
        calc _ ≤ _ := this
          _ = _ := by ring)
  have h2 : S.En ε σ (Y + s) / |S.P (Y + s)| ≤ S.Esup ε σ := le_csSup hb ⟨Y + s, hYs, rfl⟩
  have hpos : 0 < |S.P (Y + s)| := abs_pos.mpr (hP.2 _ hYs)
  rw [div_le_iff₀ hpos] at h2
  have hEn0 : 0 ≤ S.En ε σ (Y + s) := integral_nonneg (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 _ hYs ω a).le (by positivity))))
  have hE0 : 0 ≤ S.Esup ε σ := by
    by_contra h
    push_neg at h
    nlinarith
  have h3 : S.Esup ε σ * |S.P (Y + s)| ≤ S.Esup ε σ * (CP * |S.P Y|) := mul_le_mul_of_nonneg_left (hPR Y s hY hYs) hE0
  have hk : 0 ≤ (1 + CR) ^ 2 * Cd := by positivity
  calc S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := h1
    _ ≤ (1 + CR) ^ 2 * Cd * (S.Esup ε σ * (CP * |S.P Y|)) := mul_le_mul_of_nonneg_left (le_trans h2 h3) hk
    _ = C7 CR Cd CP * S.Esup ε σ * |S.P Y| := by unfold C7; ring
end Formalism.FourierDecayAlt.P.LEx2.A
