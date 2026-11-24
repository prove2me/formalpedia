-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_smul_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:42.899655+00:00
-- url     : https://prove2.me/submissions/c23fba31-e68c-49b6-932e-979f222fc45d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_basis_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_repr_mem_pK_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pow_zero_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
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
theorem _root_.solution {κ : Type} [Fintype κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (x : V) :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) ↔
      ∀ i, a.repr x i ∈ pK K 𝔭 k := by
  constructor
  · intro hx i
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n hn =>
      have h1 : algebraMap (𝓞 K) K r ∈ pK K 𝔭 k := LocF.le_locF 𝔭 _ ⟨r, hr, rfl⟩
      have h2 := mul_mem_pK h𝔭 h1 (repr_mem_pK_zero a h𝔭 hn i)
      rw [← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simpa using h2
    | add x _ y _ hx hy =>
      rw [map_add, Finsupp.add_apply]
      exact (pK K 𝔭 k).add_mem hx hy
  · intro hx
    rw [← a.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h0 : a i ∈ extP K 𝔭 ^ 0 • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) := by
      rw [pow_zero_smul]
      exact basis_mem_locF a 𝔭 i
    simpa using smul_mem_smul h𝔭 _ (hx i) h0
end Formalism.HermitianLattices.Ext.L3.D2
