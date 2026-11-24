-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.zinv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:17.863521+00:00
-- url     : https://prove2.me/submissions/04ed2e5e-c3a3-4e9f-9e97-096b6e930a28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_normSq_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_zinv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {c : ℝ} (hc : 0 < c) (m j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | c ≤ Complex.normSq z}, ‖iteratedFDeriv ℝ j (zinv c m) z‖ ≤ B := by
  refine ⟨‖∏ i ∈ Finset.range j, ((((-(m : ℤ)) : ℤ) : ℂ) - (i : ℂ))‖ * (Real.sqrt c)⁻¹ ^ (m + j),
    fun z hz => ?_⟩
  have hz' : c ≤ Complex.normSq z := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz'
    linarith
  have hev : zinv c m =ᶠ[𝓝 z] fun w : ℂ => w⁻¹ ^ m := by
    have hopen : IsOpen {w : ℂ | c / 2 < Complex.normSq w} :=
      isOpen_lt continuous_const normSq_cd.continuous
    have hmem : z ∈ {w : ℂ | c / 2 < Complex.normSq w} := by
      show c / 2 < Complex.normSq z
      linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact zinv_eq hc m (le_of_lt hw)
  have hcd : ContDiffAt ℂ ∞ (zinv c m) z :=
    ((contDiffAt_inv ℂ hz0).pow m).congr_of_eventuallyEq hev
  have hR : ‖iteratedFDeriv ℝ j (zinv c m) z‖ = ‖iteratedFDeriv ℂ j (zinv c m) z‖ := by
    rw [← (contDiffAt_infty.1 hcd j).restrictScalars_iteratedFDeriv, Function.comp_apply,
      ContinuousMultilinearMap.norm_restrictScalars]
  have hfz : (fun w : ℂ => w⁻¹ ^ m) = fun w : ℂ => w ^ (-(m : ℤ)) := by
    funext w
    rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  rw [hR, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hev.iteratedDeriv_eq, hfz, iteratedDeriv_eq_iterate,
    iter_deriv_zpow, norm_mul, norm_zpow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hzn : Real.sqrt c ≤ ‖z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hz'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [show (-(m : ℤ) - (j : ℤ)) = -((m + j : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (inv_anti₀ hsc hzn) _
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
