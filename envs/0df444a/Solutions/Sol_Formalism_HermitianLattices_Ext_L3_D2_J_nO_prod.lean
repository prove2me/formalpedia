-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.nO_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:34.854799+00:00
-- url     : https://prove2.me/submissions/e797ba9a-5d0a-4041-86b0-c188bd241d0a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_one_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_mul_mem_pK_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_nO_one
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
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
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type} (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ∈ pK K 𝔭 0 ∧ z i ≠ 0) :
    (∏ i ∈ s, z i) ∈ pK K 𝔭 0 ∧ nO 𝔭 (∏ i ∈ s, z i) = ∏ i ∈ s, nO 𝔭 (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨one_mem_pK (K := K) 𝔭, nO_one (K := K) h𝔭⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ⟨mul_mem_pK_zero h𝔭 (hz i).1 ih.1, by rw [nO_mul h𝔭 (hz i).1 (hz i).2 ih.1, ih.2]⟩
end Formalism.HermitianLattices.Ext.L3.D2.J
