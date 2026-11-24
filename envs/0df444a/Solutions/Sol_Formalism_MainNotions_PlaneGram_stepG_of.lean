-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:16.371049+00:00
-- url     : https://prove2.me/submissions/05532bf7-7995-48de-8b2b-c3aaef9807a4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_gaR_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_gaR_neg_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_approx_gaR
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_dg_labels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hV2 : V2 K) : StepG K v p := by
  intro _hD D hV cst gam hDig
  have Hp := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ 1 (Or.inl rfl)
  have Hm := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ (-1) (Or.inr rfl)
  choose gp hp1 hp2 hp3 using Hp
  choose gm hm1 hm2 hm3 using Hm
  refine ⟨fun ζ => gp (D.labF ζ) ζ, fun ζ => gm (D.labF ζ) ζ, fun ζ => hp1 _ ζ, fun ζ => hm1 _ ζ, ?_, ?_⟩
  · intro ζ hζ
    constructor
    · have := hp3 (D.labF ζ) hζ ζ
      rw [D.gaR_one, AddValuation.map_sub_swap] at this
      exact this
    · have := hm3 (D.labF ζ) hζ ζ
      rw [D.gaR_neg_one, AddValuation.map_sub_swap] at this
      exact this
  · intro S hS θ Z hZ
    have e : θ - 12 * (D.c : ℝ) = θ - ((12 * D.c : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact ⟨vala_dg_labels D gp _ hp2 S hS θ Z hZ, vala_dg_labels D gm _ hm2 S hS θ Z hZ⟩
end Formalism.MainNotions.PlaneGram
