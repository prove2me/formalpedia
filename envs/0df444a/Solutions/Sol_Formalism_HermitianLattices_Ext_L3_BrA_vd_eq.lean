-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.vd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.803515+00:00
-- url     : https://prove2.me/submissions/c8b9d971-af5c-4709-a7bb-3a6f7aac9b7f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_map_le_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_eq_map
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
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BrA
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    vd h L 𝔭 = sSup {e : ℕ | discrF F h L ≤ 𝔭 ^ e} := by
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [discrIdeal_eq_map hF hs, map_le_extP_pow]
end Formalism.HermitianLattices.Ext.L3.BrA
