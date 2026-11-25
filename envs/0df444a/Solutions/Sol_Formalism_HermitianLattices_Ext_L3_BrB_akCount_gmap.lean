-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrB.akCount_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:55.506796+00:00
-- url     : https://prove2.me/submissions/f2c676af-c610-4d1f-9ffb-3f204138d977

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumLocRepsEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_akCount_congr

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.BrB
theorem _root_.solution {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) : akCount h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 k = akCount h T 𝔭 k :=
  akCount_congr (A := T) (B := Formalism.HermitianLatticesTheory.gmap g T) ((g.restrictScalars (𝓞 K)).submoduleMap T)
    (fun x y => hg (x : V) (y : V)) 𝔭 k
end Formalism.HermitianLattices.Ext.L3.BrB
