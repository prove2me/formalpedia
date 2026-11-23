-- Prove2me | solution 1 for Formalism.L2.Host.HChar.val_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:16.617324+00:00
-- url     : https://prove2.me/submissions/44b8c99a-e84d-4c2d-8c83-6c10a492afa9

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Theorems.Thm_Formalism_L2_Host_unif_spec

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (x : (v.adicCompletion L)ˣ) (hx : IsUnifAt v x) :
    χ.loc v x = χ.val v := by
  have hu : IsUnifAt v (atFin v (unif v)) := unif_spec v
  have hunit : IsUnitAt v (x * (atFin v (unif v))⁻¹) := by
    unfold IsUnitAt
    unfold IsUnifAt at hx hu
    rw [Units.val_mul, map_mul, hx, Units.val_inv_eq_inv_val, map_inv₀, hu,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h1 := h _ hunit
  show χ.loc v x = χ.loc v (atFin v (unif v))
  calc χ.loc v x = χ.loc v (x * (atFin v (unif v))⁻¹) * χ.loc v (atFin v (unif v)) := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = χ.loc v (atFin v (unif v)) := by rw [h1, one_mul]
end Formalism.L2.Host.HChar
