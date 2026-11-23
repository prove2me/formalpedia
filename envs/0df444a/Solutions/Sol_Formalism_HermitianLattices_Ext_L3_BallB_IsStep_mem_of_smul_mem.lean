-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.IsStep.mem_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:54.71069+00:00
-- url     : https://prove2.me/submissions/e82c5f60-b0ba-4cbe-8bf7-d61e700cbee8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal

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
open Formalism.HermitianLattices.Ext.L3.BallB.IsStep
variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}
omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB.IsStep
theorem _root_.solution (S : IsStep P A B y) (hP : P.IsMaximal) {c : 𝓞 K} (hc : c • y ∈ A) :
    c ∈ P := by
  by_contra hcP
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  apply S.notMem
  have e : y = r • (c • y) + π • y := by
    rw [smul_smul, ← add_smul, hrc, one_smul]
  rw [e]
  exact A.add_mem (A.smul_mem r hc) (S.smul π hπ)
end Formalism.HermitianLattices.Ext.L3.BallB.IsStep
