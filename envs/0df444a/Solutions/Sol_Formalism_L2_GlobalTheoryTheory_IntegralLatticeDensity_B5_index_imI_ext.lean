-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:43.976707+00:00
-- url     : https://prove2.me/submissions/2e8ad3e8-fe5e-4296-b4ae-593734b9a240

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_image_ideal

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
theorem _root_.solution {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) ^
        Module.finrank ℚ E * (FractionalIdeal.absNorm J : ℚ) ^ Module.finrank ℚ F =
      |Algebra.norm ℚ s| ^ Module.finrank ℚ E := by
  have haux := index_image_ideal J s hs
  have hJ : (FractionalIdeal.absNorm J : ℚ) =
      (Ideal.absNorm J.num : ℚ) / |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| := by
    rw [FractionalIdeal.absNorm_eq, Int.cast_abs, Algebra.coe_norm_int]
  have hD : |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ≠ 0 := by
    refine abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero J.den)
  have hf : Module.finrank ℚ F = Module.finrank ℚ E * Module.finrank E F :=
    (Module.finrank_mul_finrank ℚ E F).symm
  rw [hJ, hf, div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero _ hD),
    mul_comm (Module.finrank ℚ E) (Module.finrank E F), pow_mul, pow_mul, ← mul_pow, ← mul_pow, haux]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
