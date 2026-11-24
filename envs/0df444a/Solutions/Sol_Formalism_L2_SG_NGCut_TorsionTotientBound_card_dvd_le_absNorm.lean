-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.card_dvd_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:58.674224+00:00
-- url     : https://prove2.me/submissions/041b5ad1-a247-40f6-8d97-7e9bfddde680

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_two_le_absNorm_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (M : Ideal (𝓞 E)) (hM : M ≠ ⊥) (D : Finset (Ideal (𝓞 E)))
    (hD : ∀ I ∈ D, I ∣ M) : D.card ≤ Ideal.absNorm M := by
  classical
  have hI0 : ∀ I ∈ D, I ≠ ⊥ := fun I hI h => hM (by obtain ⟨c, hc⟩ := hD I hI; rw [hc, h, Ideal.bot_mul])
  have hinj : Set.InjOn (fun I => UniqueFactorizationMonoid.normalizedFactors I) (D : Set (Ideal (𝓞 E))) := by
    intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hI0 I hI), ← Ideal.prod_normalizedFactors_eq_self (hI0 J hJ)]
    exact congrArg Multiset.prod h
  have hsub : D.image (fun I => UniqueFactorizationMonoid.normalizedFactors I) ⊆
      (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset := by
    intro s hs
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hs
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (hI0 I hI) hM).1 (hD I hI)
  have h1 : D.card ≤ 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := by
    calc D.card = (D.image fun I => UniqueFactorizationMonoid.normalizedFactors I).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M).powerset := Multiset.toFinset_card_le _
      _ = 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := Multiset.card_powerset _
  have h2 : 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) ≤ Ideal.absNorm M := by
    have hprod : Ideal.absNorm M =
        ((UniqueFactorizationMonoid.normalizedFactors M).map Ideal.absNorm).prod := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hM]
      exact map_multiset_prod Ideal.absNorm _
    rw [hprod, ← Multiset.card_map Ideal.absNorm]
    refine Multiset.pow_card_le_prod fun n hn => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hn
    have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact two_le_absNorm_prime (Ideal.isPrime_of_prime hpr) hpr.ne_zero
  exact h1.trans h2
end Formalism.L2.SG.NGCut.TorsionTotientBound
