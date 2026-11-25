-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.natAbs_discr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:57.723748+00:00
-- url     : https://prove2.me/submissions/70b3f2dd-8ab9-406e-b240-2fa742150ac2

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent

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
    [Algebra K E] (d : ℕ) (hdK : NumberField.discr K = -(d : ℤ)) :
    (NumberField.discr E).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) * d ^ Module.finrank K E := by
  rw [← absNorm_differentIdeal E (𝓞 E),
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E), map_mul,
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K (𝓞 K), hdK,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
  simp
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
