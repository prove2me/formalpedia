-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.RedC.mk_eq_redEnd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:26.489883+00:00
-- url     : https://prove2.me/submissions/e393bb4a-68bd-4b2f-b785-f6d263a870df

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_redEnd_mk

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.RedC
namespace Formalism.HermitianLattices.Ext.L3.D2.RedC
theorem _root_.solution {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
  rw [redEnd_mk, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl
end Formalism.HermitianLattices.Ext.L3.D2.RedC
