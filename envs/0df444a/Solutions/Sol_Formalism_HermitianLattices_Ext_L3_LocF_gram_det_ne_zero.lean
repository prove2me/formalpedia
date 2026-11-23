-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.gram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:11.918942+00:00
-- url     : https://prove2.me/submissions/365f7e25-76d1-4f32-95e5-ebc390dbc16a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (hd : ∀ x, h x x = 0 → x = 0) (x : Fin n → V)
    (hli : LinearIndependent K x) : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : ∀ i, h (x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [← gram_mulVec h x v i, hv, Pi.zero_apply]
  have e' : ∀ i, h (v i • x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
  have hy : h (∑ j, v j • x j) (∑ j, v j • x j) = 0 := by
    have hs : h (∑ j, v j • x j) = ∑ j, h (v j • x j) := map_sum h _ _
    rw [hs, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => e' i
  have := Fintype.linearIndependent_iff.mp hli v (hd _ hy)
  exact hv0 (funext this)
end Formalism.HermitianLattices.Ext.L3.LocF
