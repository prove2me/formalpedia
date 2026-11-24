-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerDecompTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:26.425788+00:00
-- url     : https://prove2.me/submissions/013e00aa-a650-41f1-bcf1-469e756b894e

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_stab_fix
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_sgn_eq_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_decomposition_subgroup_index
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_efg_L
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


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
theorem _root_.solution (hG : LayerGalois) : LayerDecompTwo := by
  intro n q d hn hqd L _ _ ζ a b h P _ _ σ
  obtain ⟨he, hf, -⟩ := efg_L hG hn hqd h P
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  let φ : Gal(L/ℚ) →* GalL n := MonoidHom.mk' (galMap h.1 a b) hmul
  have hle : MulAction.stabilizer Gal(L/ℚ) P ≤ (D2 n).comap φ := by
    intro τ hτ
    show galMap h.1 a b τ ∈ D2 n
    rw [D2, MonoidHom.mem_ker]
    exact (sgn_eq_one_iff τ b).mpr (stab_fix b c' hb P τ hτ)
  have hcardS : Nat.card (MulAction.stabilizer Gal(L/ℚ) P) = 2 ^ n := by
    rw [card_stabilizer_eq (G := Gal(L/ℚ)) (span {(2 : ℤ)}) P,
      ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ),
      inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), he, hf, ← pow_succ]
    congr 1
    omega
  have hcardD : Nat.card ((D2 n).comap φ) = 2 ^ n := by
    have h1 := Subgroup.card_mul_index ((D2 n).comap φ)
    rw [Subgroup.index_comap_of_surjective _ hbij.2, decomposition_subgroup_index, IsGalois.card_aut_eq_finrank, hdeg,
      pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right two_pos h1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, hcardD])
  rw [heq]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition
