-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.under_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:23.13191+00:00
-- url     : https://prove2.me/submissions/79d21a8a-1b3b-458c-b8e9-2a8a78c2560b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by
  intro h
  have hPb : P = ⊥ := Ideal.eq_bot_of_comap_eq_bot h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K) hPb
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
