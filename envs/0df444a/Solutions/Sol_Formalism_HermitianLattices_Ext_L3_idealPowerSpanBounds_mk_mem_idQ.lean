-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mk_mem_idQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:22.634299+00:00
-- url     : https://prove2.me/submissions/1a40bdf0-4ec5-4ceb-9701-fa3ae440bd8b

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : j ≤ k) {z : 𝓞 K} :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) z ∈ idQ K 𝔭 k j ↔ z ∈ extP K 𝔭 ^ j := by
  rw [mem_idQ]
  constructor
  · rintro ⟨z', hz', he⟩
    rw [Ideal.Quotient.eq] at he
    have h1 : z' - z ∈ extP K 𝔭 ^ j := Ideal.pow_le_pow_right hjk he
    have h2 : z = z' - (z' - z) := by ring
    rw [h2]
    exact Ideal.sub_mem _ hz' h1
  · intro hz
    exact ⟨z, hz, rfl⟩
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
