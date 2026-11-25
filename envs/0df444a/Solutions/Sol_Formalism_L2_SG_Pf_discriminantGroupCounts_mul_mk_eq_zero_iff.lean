-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.mul_mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:56.630432+00:00
-- url     : https://prove2.me/submissions/57f5bf39-21fd-4990-91a9-3c8f706efdaf

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) (w : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) w * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0 ↔
      w ∈ extP K 𝔭 ^ (k - e) := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  have haP : algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ e := by
    have h1 : algebraMap (𝓞 F) (𝓞 K) a ∈ (𝔭 ^ e).map (algebraMap (𝓞 F) (𝓞 K)) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h1
    exact h1
  constructor
  · intro hw
    obtain ⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
    have hJP : J ⊔ 𝔭 = ⊤ := by
      by_contra hne
      have hle : J ≤ 𝔭 := le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)
      apply ha'
      have h1 : a ∈ 𝔭 ^ e * J := by
        rw [← hJ]
        exact Ideal.mem_span_singleton_self a
      rw [pow_succ]
      exact Ideal.mul_mono_right hle h1
    have hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} =
        extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K)) := by
      have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ
      rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow] at h1
      exact h1
    have hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K))) := by
      apply IsCoprime.pow_left
      rw [Ideal.isCoprime_iff_sup_eq]
      have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP
      rw [Ideal.map_sup, Ideal.map_top] at h1
      rw [sup_comm]
      exact h1
    have hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0 := by
      intro x hx
      have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx,
          map_zero]
      rw [map_eq_zero_iff _ (algebraMap F K).injective] at h1
      exact IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])
    have ha0 : a ≠ 0 := fun h => ha' (h ▸ Ideal.zero_mem _)
    have hPe : extP K 𝔭 ^ e ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      intro h0
      rw [h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot] at hspan
      exact ha0 (hιinj a hspan)
    have hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣
        (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e := by
      rw [← hkP]
      have h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a} :=
        Ideal.dvd_span_singleton.mpr hw
      rw [← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e),
        ← mul_assoc] at h2
      exact h2
    rw [mul_dvd_mul_iff_right hPe] at hdiv
    exact Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)
  · intro hw
    rw [hkP]
    exact Ideal.mul_mem_mul hw haP
end Formalism.L2.SG.Pf.discriminantGroupCounts
