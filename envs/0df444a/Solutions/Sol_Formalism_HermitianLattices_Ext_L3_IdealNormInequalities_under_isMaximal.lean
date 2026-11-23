-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.under_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:24.569911+00:00
-- url     : https://prove2.me/submissions/26321973-53ff-4840-88ac-975d9c6a0c9f

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (P.under ℤ).IsMaximal := by
  haveI := hP
  exact Ideal.IsMaximal.under ℤ P
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
