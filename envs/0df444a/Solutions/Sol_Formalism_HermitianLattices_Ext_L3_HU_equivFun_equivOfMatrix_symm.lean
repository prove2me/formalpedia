-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.equivFun_equivOfMatrix_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:59.313987+00:00
-- url     : https://prove2.me/submissions/39cf2e91-265a-4b37-9a4b-5c1fe06e1e1a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_toLin

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
theorem _root_.solution (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun ((equivOfMatrix b G G' hG).symm x) = G' *ᵥ b.equivFun x := equivFun_toLin b G' x
end Formalism.HermitianLattices.Ext.L3.HU
