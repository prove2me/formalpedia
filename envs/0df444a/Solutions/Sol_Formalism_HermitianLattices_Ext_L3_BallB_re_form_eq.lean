-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.re_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:31.657939+00:00
-- url     : https://prove2.me/submissions/1fcd78cf-2060-4875-ae9a-8edb0064f3b9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_form_eq

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
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (φ : K →+* ℂ) :
    (φ (h x x)).re = ∑ i, (φ (h (b i) (b i))).re * Complex.normSq (φ (b.repr x i)) := by
  rw [form_eq b ho x, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, mul_comm]
end Formalism.HermitianLattices.Ext.L3.BallB
