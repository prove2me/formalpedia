-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:21.656242+00:00
-- url     : https://prove2.me/submissions/dae359f0-0042-4ed5-99eb-a9d68568e052

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
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
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V) :
    h x x = ∑ i, star (b.repr x i) * b.repr x i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    simp [ho j i hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi
end Formalism.HermitianLattices.Ext.L3.BallB
