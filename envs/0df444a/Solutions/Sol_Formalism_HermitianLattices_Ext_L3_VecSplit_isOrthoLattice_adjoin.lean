-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.isOrthoLattice_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:13.632094+00:00
-- url     : https://prove2.me/submissions/3257cd21-a80f-4fb1-880d-d77d13fbdfbd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3
namespace VecSplit
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := S.isOrthoLattice_adjoin' hs h1 hI'
end VecSplit
end Formalism.HermitianLattices.Ext.L3
