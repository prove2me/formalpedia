-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.real_imp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:19.329472+00:00
-- url     : https://prove2.me/submissions/1ccfbf3d-65ff-4a11-9a35-3ff4bfa01c6b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (q ε c' : ℝ) (j t : ℕ) (hq : 0 < q) (hε : ε ^ 2 = 1) :
    (q ^ (2 * (t + 1)) * c') / q ^ ((j + 2) * (2 * (t + 1) - 1)) =
      (ε * (q ^ t)⁻¹) ^ 2 * (c' / q ^ (j * (2 * (t + 1) - 1))) := by
  have hq0 : q ≠ 0 := hq.ne'
  have h1 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have h2 : (j + 2) * (2 * t + 1) = j * (2 * t + 1) + (2 * t + 2) + 2 * t := by ring
  rw [h1, h2, pow_add, pow_add, mul_pow, hε, inv_pow]
  field_simp
  ring
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
