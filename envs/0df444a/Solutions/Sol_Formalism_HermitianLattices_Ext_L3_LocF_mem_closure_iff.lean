-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.mem_closure_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:30.776842+00:00
-- url     : https://prove2.me/submissions/7005d2ce-7b7e-409a-b7be-47678d6dec29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (s : 𝓞 K) :
    s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} ↔
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨t, ht, rfl⟩ := iha
      obtain ⟨u, hu, rfl⟩ := ihb
      exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, map_mul _ _ _⟩
  · intro hs
    exact Submonoid.subset_closure hs
end Formalism.HermitianLattices.Ext.L3.LocF
