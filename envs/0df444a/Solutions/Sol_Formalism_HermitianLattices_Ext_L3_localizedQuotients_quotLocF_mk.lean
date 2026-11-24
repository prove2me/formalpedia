-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.quotLocF_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:29.602883+00:00
-- url     : https://prove2.me/submissions/e2d49d06-6274-443e-9944-0a0b8687a03a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) (y : ↥L)
    (hy : (y : V) ∈ locF 𝔭 L) :
    quotLocF h𝔭 L k (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨(y : V), hy⟩ := rfl
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
