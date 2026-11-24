-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.excSum_leOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.759182+00:00
-- url     : https://prove2.me/submissions/be94acf0-6819-48b8-932f-806e31b6d125

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {ι : Type*} [Fintype ι] (B : ι → Finset ℝ) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcard : ∀ i, (B i).card ≤ 1) (huniq : ∀ i j, (B i).Nonempty → (B j).Nonempty → i = j)
    (hf : ∀ i, ∀ β ∈ B i, f β ≤ M) : ∑ i, ∑ β ∈ B i, f β ≤ M := by
  by_cases h : ∃ i, (B i).Nonempty
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · have h1 : (B i).card = 1 := le_antisymm (hcard i) (Finset.card_pos.mpr hi)
      obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp h1
      rw [hβ, Finset.sum_singleton]
      exact hf i β (by rw [hβ]; exact Finset.mem_singleton_self β)
    · intro j _ hji
      have : ¬ (B j).Nonempty := fun hj => hji (huniq j i hj hi)
      rw [Finset.not_nonempty_iff_eq_empty.mp this, Finset.sum_empty]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · have h' : ∀ i, ¬ (B i).Nonempty := fun i hi => h ⟨i, hi⟩
    have : ∑ i, ∑ β ∈ B i, f β = 0 := Finset.sum_eq_zero (fun i _ => by
      rw [Finset.not_nonempty_iff_eq_empty.mp (h' i), Finset.sum_empty])
    rw [this]
    exact hM
end Formalism.HermitianLattices.Ext.SupplyAP
