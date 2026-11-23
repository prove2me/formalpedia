-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:44.906077+00:00
-- url     : https://prove2.me/submissions/8016d786-0a77-4074-bd18-2d9f2fc1e2fe

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
theorem _root_.solution {n : ℕ} {e : Fin n → V} (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ c : Fin n → K, ∑ i, c i • e i = x :=
  (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)
end Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
