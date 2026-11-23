-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mul_eq_zero_idQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:57.499926+00:00
-- url     : https://prove2.me/submissions/3b911283-084d-407f-8c95-948562381d72

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_idQ

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : k ≤ 2 * j)
    {a b : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) (hb : b ∈ idQ K 𝔭 k j) : a * b = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_idQ.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_idQ.mp hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : x * y ∈ extP K 𝔭 ^ (j + j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right (by omega) h1
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
