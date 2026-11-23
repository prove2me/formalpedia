-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:17.992605+00:00
-- url     : https://prove2.me/submissions/307840ec-e048-4c05-a2de-447083e9d8dd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_map_ne_bot_of_isMaximal


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := by
  have h0 : extP K 𝔭 ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  first
  | exact Ideal.finiteQuotientOfFreeOfNeBot _ h0
  | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
