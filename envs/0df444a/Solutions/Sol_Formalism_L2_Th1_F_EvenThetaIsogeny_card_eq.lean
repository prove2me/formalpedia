-- Prove2me | solution 1 for Formalism.L2.Th1.F.EvenThetaIsogeny.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:32.177169+00:00
-- url     : https://prove2.me/submissions/9d27ce92-38fb-4e35-938e-cbd8ad7cbff7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MemOfDenEqZero
import Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_mem_of_eq
import Theorems.Thm_Formalism_L2_Th1_F_kernel_reps_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EvenThetaIsogeny
open IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α t : ℂ) (T : Finset ℂ)
namespace Formalism.L2.Th1.F.EvenThetaIsogeny
theorem _root_.solution (hα : α ≠ 0) (hst : MulStable L α) (h2t : 2 * t ∈ L.lattice)
    (hT : IsFibreReps L α t T) : 2 * (T.card : ℝ) = Complex.normSq α := by
  classical
  obtain ⟨hT1, hT2, hT3⟩ := hT
  obtain ⟨Q₀, hQ₀, -⟩ := hT3 (t / α) (mem_of_eq L (zero_mem _) (by field_simp; ring))
  have hinj1 : Function.Injective (fun Q : ℂ => Q - Q₀) := sub_left_injective
  have hinj2 : Function.Injective (fun Q : ℂ => -Q - Q₀) := fun a b h => by
    have h' : -a - Q₀ = -b - Q₀ := h
    linear_combination -h'
  have hno : ∀ Q ∈ T, ∀ Q' ∈ T, Q + Q' ∉ L.lattice := by
    intro Q hQ Q' hQ' h
    have h' := hT2 Q hQ Q' hQ' (Or.inr h)
    rw [← h'] at h
    exact (hT1 Q hQ).2 (mem_of_eq L h (by ring))
  have hdisj : Disjoint ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀))
      (T.image (fun Q : ℂ => -Q - Q₀)) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q', hQ', h⟩ := Finset.mem_image.1 hP'
    exact hno Q (Finset.mem_of_mem_erase hQ) Q' hQ'
      (mem_of_eq L (zero_mem _) (by linear_combination -h))
  have hker : IsKerReps L α
      ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀) ∪ T.image (fun Q : ℂ => -Q - Q₀)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro P hP
      rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        have hQT := Finset.mem_of_mem_erase hQ
        exact ⟨mem_of_eq L (sub_mem (hT1 Q hQT).1 (hT1 Q₀ hQ₀).1) (by ring),
          fun h => Finset.ne_of_mem_erase hQ (hT2 Q hQT Q₀ hQ₀ (Or.inl h))⟩
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        exact ⟨mem_of_eq L (neg_mem (add_mem (add_mem (hT1 Q hQ).1 (hT1 Q₀ hQ₀).1) h2t)) (by ring),
          fun h => hno Q hQ Q₀ hQ₀ (mem_of_eq L (neg_mem h) (by ring))⟩
    · intro P hP P' hP' h
      rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        rw [hT2 Q (Finset.mem_of_mem_erase hQ) Q' (Finset.mem_of_mem_erase hQ')
          (Or.inl (mem_of_eq L h (by ring)))]
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        exact absurd (mem_of_eq L h (by ring)) (hno Q (Finset.mem_of_mem_erase hQ) Q' hQ')
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        exact absurd (mem_of_eq L (neg_mem h) (by ring)) (hno Q hQ Q' (Finset.mem_of_mem_erase hQ'))
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        rw [hT2 Q hQ Q' hQ' (Or.inl (mem_of_eq L (neg_mem h) (by ring)))]
    · intro z hz hz0
      obtain ⟨Q, hQ, h⟩ := hT3 (z + Q₀) (mem_of_eq L (add_mem hz (hT1 Q₀ hQ₀).1) (by ring))
      rcases h with h | h
      · refine ⟨Q - Q₀, Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_erase.2 ⟨fun hne => hz0 (mem_of_eq L h (by rw [hne]; ring)), hQ⟩)),
          mem_of_eq L h (by ring)⟩
      · exact ⟨-Q - Q₀, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ),
          mem_of_eq L h (by ring)⟩
  have hcard := kernel_reps_card L α _ hα hst hker
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2, Finset.card_erase_of_mem hQ₀] at hcard
  have hpos : 1 ≤ T.card := Finset.card_pos.2 ⟨Q₀, hQ₀⟩
  rw [← hcard]
  push_cast [Nat.cast_sub hpos]
  ring
end Formalism.L2.Th1.F.EvenThetaIsogeny
