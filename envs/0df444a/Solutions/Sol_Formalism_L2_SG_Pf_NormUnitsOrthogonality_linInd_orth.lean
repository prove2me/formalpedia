-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NormUnitsOrthogonality.linInd_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:19.636287+00:00
-- url     : https://prove2.me/submissions/e135bd6e-65b7-44be-b4ac-568e66119139

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DualFormInverse
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality
theorem _root_.solution {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs
  rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'
end Formalism.L2.SG.Pf.NormUnitsOrthogonality
