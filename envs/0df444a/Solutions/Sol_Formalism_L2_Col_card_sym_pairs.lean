-- Prove2me | solution 1 for Formalism.L2.Col.card_sym_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:20.322809+00:00
-- url     : https://prove2.me/submissions/f57c37bf-eac0-4b56-b99a-947a9cae8593

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_card_lt_pairs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution (k rS : ℕ) (hn : rS + k < n) :
    Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)} = n * (n - 1) / 2 - k := by
  have hA : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := card_lt_pairs n
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hA ⊢
  rw [← hA]
  have hsub : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) ⊆
      Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    show p.1.val < p.2.val
    omega
  have hB : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k).card = k := by
    rw [← Fintype.card_subtype]
    have e : {p : Fin n × Fin n // rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k} ≃ Fin k :=
      { toFun := fun p => ⟨p.1.1.val - rS, by obtain ⟨h1, h2, h3⟩ := p.2; omega⟩
        invFun := fun i => ⟨(⟨rS + i.val, by omega⟩, ⟨rS + k, hn⟩), Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨a, b⟩, h1, h2, h3⟩ := p
          dsimp only at h1 h2 h3
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            show rS + (a.val - rS) = a.val
            omega
          · apply Fin.ext
            show rS + k = b.val
            omega
        right_inv := fun i => by
          apply Fin.ext
          show rS + i.val - rS = i.val
          omega }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hsd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
        (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hsd, Finset.card_sdiff_of_subset hsub, hB]
end Formalism.L2.Col
