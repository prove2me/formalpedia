-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mem_smul_locF_iff_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:58.692798+00:00
-- url     : https://prove2.me/submissions/7d9eaeae-fbcd-43c5-91b1-eba30942781f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_smul_basis_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_locF_iff_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ) (x : V) :
    x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) ↔ ∀ i, InP 𝔭 k (b.equivFun x i) := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y hy =>
      intro i
      rw [← algebraMap_smul K r, map_smul, Pi.smul_apply, smul_eq_mul]
      exact (inP_jK hr).mul (l := 0) ((mem_locF_iff_repr b y).1 hy i)
    | add y _ z _ hy hz =>
      intro i
      rw [map_add]
      exact (hy i).add (hz i)
  · intro hx
    rw [← b.sum_equivFun x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht, z, hz, e⟩ := hx i
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    have h1 : (jK (ι t))⁻¹ ∈ SP K 𝔭 := mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ ht0]⟩
    have h2 : b.equivFun x i • b i = z • ((jK (ι t))⁻¹ • b i) := by
      rw [← algebraMap_smul K z, smul_smul, e]
      congr 1
      field_simp
    rw [h2]
    exact Submodule.smul_mem_smul hz (smul_basis_mem b h1 i)
end Formalism.HermitianLattices.Ext.L3.HU
