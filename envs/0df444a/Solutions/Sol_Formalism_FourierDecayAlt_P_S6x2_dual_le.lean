-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.dual_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.111707+00:00
-- url     : https://prove2.me/submissions/52679f07-8ca4-4a74-874a-5b6a7484e09b

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (h2 : PowConjStable) (h3 : Between)
    (g : ℕ) (ν : ℤ) (s : ℕ) (hg : 0 < g) :
    dualLat E g (perLat E g ν s) ≤ zsub E (dualIdl E g ν) := by
  intro x hx
  have := h1 E (dd E) (dual_one E) ν (g : ℤ) (by exact_mod_cast hg.ne') (perLat E g ν s) ?_ x ?_
  · show x ∈ dualIdl E g ν
    unfold dualIdl idl
    rw [zpow_neg_one]
    simpa using this
  · intro y hy
    refine (h3 E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (h2 E g 2 ν)).1 ?_
    show y ∈ idl E g 2 ν
    unfold idl
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    simpa using hy
  · intro y hy
    simpa using hx y hy
end Formalism.FourierDecayAlt.P.S6x2
