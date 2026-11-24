-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenB.dense_modE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:42:52.826446+00:00
-- url     : https://prove2.me/submissions/3463d1df-638a-4379-b7e7-38743bdd5a9e

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_dense_mod
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace Formalism.MainNotions.BridgeLevelGenB
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) (a : E ⊗[F] Af F) (ha : a ∈ IntAf F E) :
    ∃ b ∈ Formalism.UG.intOE E, ∃ c ∈ IntAf F E, a = b ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c := by
  have gen1 : ∀ b ∈ Formalism.UG.intOE E, b ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := fun b hb =>
    Subring.subset_closure (Or.inl ⟨⟨b, hb⟩, rfl⟩)
  have gen2 : ∀ y ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] y ∈ IntAf F E := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hgI : (g : E ⊗[F] Af F) ∈ IntAf F E := natCast_mem _ g
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨b, hb⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨b, hb, 0, zero_mem _, by simp⟩
    · obtain ⟨s, c, hc, e⟩ := dense_mod g hg y hy
      have hint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F s)) :=
        (RingOfIntegers.isIntegral_coe s).algebraMap
      refine ⟨algebraMap F E (algebraMap (𝓞 F) F s), ⟨⟨_, hint⟩, rfl⟩, (1 : E) ⊗ₜ[F] c, gen2 c hc, ?_⟩
      have e1 : (g : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (g : Af F) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
      have e2 : algebraMap F E (algebraMap (𝓞 F) F s) ⊗ₜ[F] (1 : Af F) =
          (1 : E) ⊗ₜ[F] algebraMap F (Af F) (algebraMap (𝓞 F) F s) := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Af F), TensorProduct.smul_tmul]
      show (1 : E) ⊗ₜ[F] y = _
      rw [e1, e2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b + b', add_mem hb hb', c + c', add_mem hc hc', ?_⟩
    rw [TensorProduct.add_tmul]; ring
  | neg x _ hx =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    refine ⟨-b, neg_mem hb, -c, neg_mem hc, ?_⟩
    rw [TensorProduct.neg_tmul]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b * b', mul_mem hb hb',
      b ⊗ₜ[F] (1 : Af F) * c' + c * b' ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c * c', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem (gen1 b hb) hc') (mul_mem hc (gen1 b' hb'))) (mul_mem (mul_mem hgI hc) hc')
    · rw [show (b * b') ⊗ₜ[F] (1 : Af F) = b ⊗ₜ[F] (1 : Af F) * b' ⊗ₜ[F] (1 : Af F) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
      ring
end Formalism.MainNotions.BridgeLevelGenB
