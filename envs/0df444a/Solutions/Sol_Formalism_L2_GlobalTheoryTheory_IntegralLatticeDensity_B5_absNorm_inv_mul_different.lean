-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.absNorm_inv_mul_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:40.327675+00:00
-- url     : https://prove2.me/submissions/54dfe370-e2dc-4970-8476-aa4e8435bc95

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent
import Theorems.Thm_P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0

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
theorem _root_.solution (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E))
    (h : differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * (c • 𝔟)) :
    FractionalIdeal.absNorm (((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ *
        ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ^ 2 =
      (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℚ) := by
  have hD : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    exact hD (by rw [h]; exact Submodule.bot_mul _)
  have hcoe : ∀ J : Ideal (𝓞 E), FractionalIdeal.absNorm
      ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) = (Ideal.absNorm J : ℚ) := fun J =>
    FractionalIdeal.coeIdeal_absNorm J
  have hB : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, inv_mul_cancel₀ hB, one_mul, hcoe, map_mul,
    absNorm_galois_smul' E c 𝔟]
  push_cast
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
