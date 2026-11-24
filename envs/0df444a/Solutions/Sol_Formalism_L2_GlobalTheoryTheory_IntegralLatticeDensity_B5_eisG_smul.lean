-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.eisG_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:10.997354+00:00
-- url     : https://prove2.me/submissions/5a438861-c022-4790-ae3e-44212c343876

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Homothety

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    eisG (c • Λ) k = (c ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [show (∑' w : {w : ℂ // w ∈ c • Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)) =
      ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / ((smulEquivNZ Λ c hc w : ℂ)) ^ (2 * k) from
      ((smulEquivNZ Λ c hc).tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm]
  rw [← tsum_mul_left]
  congr 1
  funext w
  show 1 / (c * w.1) ^ (2 * k) = (c ^ (2 * k))⁻¹ * (1 / w.1 ^ (2 * k))
  rw [one_div, one_div, mul_pow, mul_inv]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
