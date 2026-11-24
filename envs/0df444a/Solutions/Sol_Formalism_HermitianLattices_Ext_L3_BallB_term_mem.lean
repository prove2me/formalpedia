-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.term_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:31.902137+00:00
-- url     : https://prove2.me/submissions/b4a91eb5-a40e-495a-8bc9-493d71f5228c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_conjO_mem_conjIdeal

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {P I : Ideal (𝓞 K)} {p₁ p₂ z : 𝓞 K} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hz : z ∈ I) :
    conjO K p₁ * p₂ * z ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * I := by
  have h3 := Ideal.mul_mem_mul (Ideal.mul_mem_mul h₂ (conjO_mem_conjIdeal h₁)) hz
  rwa [mul_comm p₂ (conjO K p₁)] at h3
end Formalism.HermitianLattices.Ext.L3.BallB
