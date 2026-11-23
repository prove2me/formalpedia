-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.size_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:24.292728+00:00
-- url     : https://prove2.me/submissions/9771184e-7a98-4f53-82fb-2303eb93792a

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (D : Data E W) (Θ : ℝ) (hΘ : 1 ≤ Θ) (hS : D.SizesBelow Θ) :
    ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ 1 := by
  intro b s hb hs hbs
  refine (hS.2 b s hb hs hbs).trans ?_
  have h1 : (Θ ^ D.f)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hΘ)
  have h0 : 0 ≤ (Θ ^ D.f)⁻¹ := by positivity
  exact pow_le_one₀ h0 h1
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
