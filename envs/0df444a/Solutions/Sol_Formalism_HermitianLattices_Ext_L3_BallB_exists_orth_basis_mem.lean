-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.exists_orth_basis_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:39.775829+00:00
-- url     : https://prove2.me/submissions/40e39c4e-05d7-4888-bc09-2d538abd0bd5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_mult
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_orthBasisPos
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
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧ ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  obtain ⟨e, he, -⟩ := orthBasisPos K hK V h hs hd
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (e i)
  have hb : ∀ i, e.unitsSMul (fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i))) i =
      (n i : K) • e i := fun i => by rw [Basis.unitsSMul_apply]; rfl
  refine ⟨e.unitsSMul fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i)), fun i => ?_,
    fun i j hij => ?_⟩
  · rw [hb, Int.cast_smul_eq_zsmul]; exact hnx i
  · simp only [hb, map_smulₛₗ, LinearMap.smul_apply, he i j hij, smul_zero]
end Formalism.HermitianLattices.Ext.L3.BallB
