-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mem_locF_iff_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:23:32.025588+00:00
-- url     : https://prove2.me/submissions/eba99afd-15ce-427e-9eca-90b2d0293f53

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_smul_basis_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_coe_eq_sum
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (x : V) :
    x ∈ locF 𝔭 (spanO b) ↔ ∀ i, b.equivFun x i ∈ SP K 𝔭 := by
  constructor
  · intro hx i
    obtain ⟨t, ht, h1⟩ := (mem_locF 𝔭 _ _).1 hx
    have h2 : ι t • x = _ := coe_eq_sum b ⟨_, h1⟩
    generalize crd b ⟨_, h1⟩ = c at h2
    refine mem_SP.2 ⟨t, ht, c i, ?_⟩
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [← algebraMap_smul K (ι t), map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
      Basis.equivFun_self, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h3
    exact h3.symm
  · intro hx
    rw [← b.sum_equivFun x]
    exact Submodule.sum_mem _ fun i _ => smul_basis_mem b (hx i) i
end Formalism.HermitianLattices.Ext.L3.HU
