-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.det_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.487644+00:00
-- url     : https://prove2.me/submissions/4605c73f-3b6c-45de-9020-0534ee96fcc3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_mulVec
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {L : Submodule (𝓞 K) V} (x : Fin n → V) (hx : ∀ i, x i ∈ L)
    (hspan : Submodule.span K (Set.range x) = ⊤) (g : Matrix (Fin n) (Fin n) (𝓞 K))
    (hg : ∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) (y : V)
    (hy : ∀ i, h (x i) y ∈ (1 : Submodule (𝓞 K) K)) : g.det • y ∈ L := by
  have hy' : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  choose β hβ using fun i => Submodule.mem_one.mp (hy i)
  set G := Matrix.of fun i j => h (x i) (x j) with hGdef
  have hGg : (algebraMap (𝓞 K) K).mapMatrix g = G := by
    ext i j
    simp [RingHom.mapMatrix_apply, hg, hGdef]
  have hGc : G *ᵥ c = fun i => algebraMap (𝓞 K) K (β i) := by
    funext i
    rw [hGdef, gram_mulVec h x c i, hc, hβ]

  have hdetc : G.det • c = fun j => algebraMap (𝓞 K) K ((g.adjugate *ᵥ β) j) := by
    funext j
    have h1 : G.det • c = G.adjugate *ᵥ (G *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
      first
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | simp
    rw [h1, hGc, RingHom.map_mulVec, ← hGg, ← RingHom.map_adjugate]
    rfl
  have hdet : algebraMap (𝓞 K) K g.det = G.det := by rw [RingHom.map_det, hGg]
  rw [← algebraMap_smul K g.det y, hdet, ← hc, Finset.smul_sum]
  have hj : ∀ j, G.det • (c j • x j) = (g.adjugate *ᵥ β) j • x j := by
    intro j
    have := congrFun hdetc j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [smul_smul, this, algebraMap_smul]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  exact L.sum_mem fun j _ => L.smul_mem _ (hx j)
end Formalism.HermitianLattices.Ext.L3.LocF
