-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_invOn_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:39.540377+00:00
-- url     : https://prove2.me/submissions/45799b47-2dcd-49a2-aa48-28938405dede

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mem_invOn
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_of_ne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_edgeW_swap
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
variable {R : Type u} [CommRing R]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (w : Fin n → Fin n → R) (hw : ∀ i j, w i j = w j i)
    (g : Finset (Fin n) → R) (a : Fin n) (s : Finset (Fin n)) (ha : a ∉ s) :
    ∑ σ ∈ invOn (insert a s), edgeW w σ * g ((insert a s).filter (fun i => σ i = i)) =
      ∑ σ ∈ invOn s, edgeW w σ * g (insert a (s.filter (fun i => σ i = i))) +
        ∑ b ∈ s, w a b * ∑ σ ∈ invOn (s.erase b),
          edgeW w σ * g ((s.erase b).filter (fun i => σ i = i)) := by
  have hmaps : ∀ σ ∈ invOn (insert a s), σ a ∈ insert a s := by
    intro σ hσ
    by_contra hn
    have h1 := (mem_invOn.mp hσ).2 _ hn
    exact hn (by rw [σ.injective h1]; exact Finset.mem_insert_self _ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_insert ha]
  congr 1
  · have hset : (invOn (insert a s)).filter (fun σ => σ a = a) = invOn s := by
      ext σ
      rw [Finset.mem_filter, mem_invOn, mem_invOn]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun i hi => ?_⟩
        by_cases hia : i = a
        · rw [hia, h3]
        · exact h2 i (by simp [hia, hi])
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun i hi => h2 i fun h => hi (Finset.mem_insert_of_mem h)⟩, h2 a ha⟩
    rw [hset]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.filter_insert, if_pos ((mem_invOn.mp hσ).2 a ha)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun τ => Equiv.swap a b * τ) (fun σ => Equiv.swap a b * σ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hτ
      have hτa : τ a = a := h2 a fun h => ha (Finset.mem_of_mem_erase h)
      have hτb : τ b = b := h2 b (Finset.notMem_erase b s)
      rw [Finset.mem_filter, mem_invOn]
      refine ⟨⟨swap_mul_sq h1 (by rw [hτa, hτb]), fun i hi => ?_⟩, swap_mul_apply_left hτa⟩
      have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
      have hib : i ≠ b := fun h => his (h ▸ hb)
      rw [swap_mul_apply_of_ne hτa hτb hia hib]
      exact h2 i fun h => his (Finset.mem_of_mem_erase h)
    · intro σ hσ
      obtain ⟨hσ1, hσa⟩ := Finset.mem_filter.mp hσ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hσ1
      have hσb : σ b = a := by
        have := congrArg (fun f : Equiv.Perm (Fin n) => f a) h1
        simpa [hσa] using this
      rw [mem_invOn]
      refine ⟨swap_mul_sq h1 (by rw [hσa, hσb, Equiv.swap_comm]), fun i hi => ?_⟩
      by_cases hia : i = a
      · rw [hia, Equiv.Perm.mul_apply, hσa, Equiv.swap_apply_right]
      · by_cases hib : i = b
        · rw [hib, Equiv.Perm.mul_apply, hσb, Equiv.swap_apply_left]
        · have his : i ∉ insert a s := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨hia, fun h => hi (Finset.mem_erase.mpr ⟨hib, h⟩)⟩
          rw [Equiv.Perm.mul_apply, h2 i his, Equiv.swap_apply_of_ne_of_ne hia hib]
    · intro τ _
      simp [← mul_assoc]
    · intro σ _
      simp [← mul_assoc]
    · intro τ hτ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hτ
      have hτa : τ a = a := h2 a fun h => ha (Finset.mem_of_mem_erase h)
      have hτb : τ b = b := h2 b (Finset.notMem_erase b s)
      have hset : (insert a s).filter (fun i => (Equiv.swap a b * τ) i = i) =
          (s.erase b).filter (fun i => τ i = i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        by_cases hia : i = a
        · subst hia
          simp [swap_mul_apply_left hτa, ha, hab.symm]
        · by_cases hib : i = b
          · subst hib
            simp [swap_mul_apply_right hτb, hab]
          · simp [swap_mul_apply_of_ne hτa hτb hia hib, hia, hib]
      rw [hset, edgeW_swap w hw hab hτa hτb, mul_assoc]
end Formalism.DworkPowerSeriesWeights
