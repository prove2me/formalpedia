-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:52.826433+00:00
-- url     : https://prove2.me/submissions/9ced302f-aebc-472e-a479-aedd73d8067f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) {v : κ → K}
    (hv : ∀ i, v i ∈ SP K 𝔭) (i : κ) : (G *ᵥ v) i ∈ SP K 𝔭 :=
  (SP K 𝔭).sum_mem fun j _ => (SP K 𝔭).mul_mem (hG i j) (hv j)
end Formalism.HermitianLattices.Ext.L3.HU
