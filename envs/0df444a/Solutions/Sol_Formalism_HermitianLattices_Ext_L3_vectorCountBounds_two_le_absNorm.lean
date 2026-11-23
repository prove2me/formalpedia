-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.two_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:58.550787+00:00
-- url     : https://prove2.me/submissions/4a1ebfd4-51d9-4642-9619-e64f6c91d69d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 := by
  have h5 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact idealPowerSpanBounds.ne_bot h𝔭
  have h6 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  omega
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
