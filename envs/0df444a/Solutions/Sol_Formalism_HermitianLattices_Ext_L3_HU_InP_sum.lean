-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.InP.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:44.631013+00:00
-- url     : https://prove2.me/submissions/be7ccf96-8712-4470-ba52-fc3599eecbfc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
private theorem inP_add {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨s, hs, y, hy, hya⟩ := ha
  obtain ⟨t, ht, z, hz, hzb⟩ := hb
  refine ⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y + ι s * z,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩
  simp only [map_add, map_mul]
  linear_combination (jK (ι t)) * hya + (jK (ι s)) * hzb
end Formalism.HermitianLattices.Ext.L3.HU
end
end

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
namespace InP
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {α : Type*} (s : Finset α) (f : α → K)
    (hf : ∀ i ∈ s, InP 𝔭 k (f i)) : InP 𝔭 k (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (InP 𝔭 k) (fun a b ha hb => inP_add ha hb) (InP.zero k) hf
end InP
end Formalism.HermitianLattices.Ext.L3.HU
