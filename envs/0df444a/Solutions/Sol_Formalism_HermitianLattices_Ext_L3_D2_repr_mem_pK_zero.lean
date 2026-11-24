-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.repr_mem_pK_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:31.226374+00:00
-- url     : https://prove2.me/submissions/7959aa57-0bd6-4bb4-a956-22be687850d6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {κ : Type} (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {x : V} (hx : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) (i : κ) :
    a.repr x i ∈ pK K 𝔭 0 := by
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
  obtain ⟨z, hz⟩ := (a.mem_span_iff_repr_mem (𝓞 K) _).1 hx i
  refine (mem_pK h𝔭).2 ⟨t, ht, z, by simp, ?_⟩
  rw [hz, ← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl
end Formalism.HermitianLattices.Ext.L3.D2
