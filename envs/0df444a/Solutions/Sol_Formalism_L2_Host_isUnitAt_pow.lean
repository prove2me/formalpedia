-- Prove2me | solution 1 for Formalism.L2.Host.isUnitAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:37.275553+00:00
-- url     : https://prove2.me/submissions/b94b4c54-88a6-4ec0-be4e-1a7502b2c9b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Host
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (n : ℕ) :
    IsUnitAt v (x ^ n) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
end Formalism.L2.Host
