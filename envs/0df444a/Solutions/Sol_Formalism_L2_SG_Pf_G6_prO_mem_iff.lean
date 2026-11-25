-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G6.prO_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:48.992355+00:00
-- url     : https://prove2.me/submissions/1da12da4-3c74-4259-ab65-e2803ad59bab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscIsoOfProj

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G6
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G6
theorem _root_.solution {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by
  rw [← hX, Submodule.mem_inf]
  constructor
  · exact fun H => H.1
  · intro H
    exact ⟨H, Submodule.projection_apply_mem hc x⟩
end Formalism.L2.SG.Pf.G6
