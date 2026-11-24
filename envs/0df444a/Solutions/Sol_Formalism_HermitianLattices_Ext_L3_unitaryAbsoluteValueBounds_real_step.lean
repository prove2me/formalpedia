-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.real_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:38.397388+00:00
-- url     : https://prove2.me/submissions/ee75b399-334c-4548-9b07-797ad4ae4993

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore

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
theorem _root_.solution (q T ε β c1 cI : ℝ) (j t : ℕ) (hq : 0 < q) (hT : T = q ^ t) (hε : ε ^ 2 = 1)
    (hβ : β = 1 - ε * (q ^ (t + 1))⁻¹)
    (hc1 : c1 = q ^ (2 * (t + 1)) - (q - 1) * (q ^ (2 * (t + 1) - 1) * β)) :
    (q ^ ((2 * (t + 1) - 1) * (j + 1)) * (c1 - 1) + cI) / q ^ ((j + 2) * (2 * (t + 1) - 1)) =
      β * (1 + ε * T⁻¹) + cI / q ^ ((j + 2) * (2 * (t + 1) - 1)) := by
  subst hT hβ hc1
  have e : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hq' : q ≠ 0 := hq.ne'
  have h1 : (j + 2) * (2 * t + 1) = (2 * t + 1) * (j + 1) + (2 * t + 1) := by ring
  rw [e, h1, pow_add q ((2 * t + 1) * (j + 1)) (2 * t + 1), add_div,
    mul_div_mul_left _ _ (pow_ne_zero _ hq')]
  congr 1
  have hε2 : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  rcases hε2 with rfl | rfl
  · field_simp
    ring
  · field_simp
    ring
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
