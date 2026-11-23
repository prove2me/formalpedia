-- Prove2me | solution 1 for Formalism.L2.Host.HChar.unrAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:31.377627+00:00
-- url     : https://prove2.me/submissions/b2117463-3ef5-42ef-8f74-15a9da2fceb4

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.Host
variable (L : Type) [Field L] [NumberField L]
variable {L}
open Formalism.L2.Host.HChar
variable (χ : HChar L)
namespace Formalism.L2.Host.HChar
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : χ.UnrAt v ↔ χ.LevelLe v 0 := by
  constructor
  · intro h x hx _
    exact h x hx
  · intro h x hx
    apply h x hx
    have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
    have h1 : Valued.v ((x : v.adicCompletion L) - 1) ≤
        max (Valued.v (x : v.adicCompletion L)) (Valued.v (1 : v.adicCompletion L)) :=
      Valued.v.map_sub _ _
    rw [hx', map_one, max_self] at h1
    simpa using h1
end Formalism.L2.Host.HChar
