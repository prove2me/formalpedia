-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.two_le_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:05.562706+00:00
-- url     : https://prove2.me/submissions/8ec8ba98-7553-4f38-805f-b735b40e84e5

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_intCast_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (W : 𝓞 L) (c : ℤ) (hW : W ^ 2 = W + (c : 𝓞 L)) (hc : ¬ (2 : ℤ) ∣ c) :
    2 ≤ P.inertiaDeg ℤ := by
  have hpos := P.inertiaDeg_pos ℤ
  by_contra hlt
  have h1 : P.inertiaDeg ℤ = 1 := by omega
  have : P.LiesOver (span {((2 : ℕ) : ℤ)}) := by simpa using (inferInstance : P.LiesOver (span {(2 : ℤ)}))
  have hcard : Nat.card (𝓞 L ⧸ P) = 2 := by
    have := Ideal.pow_inertiaDeg 2 P
    rw [h1, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    exact this.symm
  obtain ⟨x, y, -, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have mem : ∀ z : 𝓞 L ⧸ P, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set (𝓞 L ⧸ P)) := huniv ▸ Set.mem_univ z
    simpa using this
  have hcP : (c : 𝓞 L) ∉ P := fun h => hc ((two_intCast_mem_iff P c).mp h)
  have hW0 : Ideal.Quotient.mk P W ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    apply hcP
    have : (c : 𝓞 L) = W * W - W := by linear_combination -hW
    rw [this]
    exact P.sub_mem (P.mul_mem_left _ h) h
  have hW1 : Ideal.Quotient.mk P W ≠ 1 := by
    intro h
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at h
    apply hcP
    have : (c : 𝓞 L) = W * (W - 1) := by linear_combination -hW
    rw [this]
    exact P.mul_mem_left _ h
  have h01 : (0 : 𝓞 L ⧸ P) ≠ 1 := zero_ne_one
  rcases mem 0 with h0 | h0 <;> rcases mem 1 with h1' | h1' <;>
    rcases mem (Ideal.Quotient.mk P W) with h2 | h2 <;>
    first
    | exact h01 (h0.trans h1'.symm)
    | exact hW0 (h2.trans h0.symm)
    | exact hW1 (h2.trans h1'.symm)
end Formalism.TwoAdicCyclotomicDecomposition
