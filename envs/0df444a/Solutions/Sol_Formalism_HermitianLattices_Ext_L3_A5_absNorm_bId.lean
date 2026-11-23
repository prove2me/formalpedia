-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.absNorm_bId
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:11.252204+00:00
-- url     : https://prove2.me/submissions/870cc125-7790-4949-a8a7-fea5e2dcbdfb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    (Ideal.absNorm (bId v) : ℝ) = nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  unfold bId nrm Finsupp.prod
  rw [map_prod]
  push_cast
  simp only [map_pow, Nat.cast_pow]
end Formalism.HermitianLattices.Ext.L3.A5
