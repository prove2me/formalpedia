-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.ker_piQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:51.177231+00:00
-- url     : https://prove2.me/submissions/3e8a5e98-2b3f-4bad-a455-3e88cdc3e8df

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_idQ

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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) : RingHom.ker (piQ K 𝔭 k) = idQ K 𝔭 (k + 1) k := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mk_mem_ker_piQ, mk_mem_idQ (Nat.le_succ k)]
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
