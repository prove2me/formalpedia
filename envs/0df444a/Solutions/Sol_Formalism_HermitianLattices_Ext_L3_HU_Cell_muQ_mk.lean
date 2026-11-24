-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cell.muQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.35188+00:00
-- url     : https://prove2.me/submissions/006bf0e8-44e6-4a93-a0cd-8546dabf4822

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction

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
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.HU.Cell
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) (a : 𝓞 K) :
    muQ (K := K) c hd (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ι d * a) := rfl
end Formalism.HermitianLattices.Ext.L3.HU.Cell
