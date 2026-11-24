-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:04:51.663167+00:00
-- url     : https://prove2.me/submissions/bb01043c-4c6e-45de-ad49-a913df8dfc87

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_inertia_fix
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_sgn_eq_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_inertia_subgroup_index
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
theorem _root_.solution (hG : LayerGalois) : LayerInertiaTwo := by
  intro n q d hn hqd L _ _ ζ a b h P _ _ σ
  obtain ⟨he, -, -⟩ := efg_L hG hn hqd h P
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q : ℤ) = 4 * c + 1 := ⟨(-(q : ℤ) - 1) / 4, by omega⟩
  have ha : a ^ 2 = ((4 * c + 1 : ℤ) : L) := by
    rw [← hc, h.2.1]
    push_cast
    ring
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * c + 1 := ⟨(-(d : ℤ) - 1) / 4, by omega⟩
  have hb : b ^ 2 = ((4 * c' + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  let φ : Gal(L/ℚ) →* GalL n := MonoidHom.mk' (galMap h.1 a b) hmul
  have hle : P.inertia Gal(L/ℚ) ≤ (I2 n).comap φ := by
    intro τ hτ
    show galMap h.1 a b τ ∈ I2 n
    rw [I2, MonoidHom.mem_ker]
    show (sgn τ a, sgn τ b) = 1
    rw [(sgn_eq_one_iff τ a).mpr (inertia_fix a c ha P τ hτ),
      (sgn_eq_one_iff τ b).mpr (inertia_fix b c' hb P τ hτ)]
    rfl
  have hcardI : Nat.card (P.inertia Gal(L/ℚ)) = 2 ^ (n - 1) := by
    rw [card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(2 : ℤ)}) P,
      ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ), he]
  have hcardD : Nat.card ((I2 n).comap φ) = 2 ^ (n - 1) := by
    have h1 := Subgroup.card_mul_index ((I2 n).comap φ)
    rw [Subgroup.index_comap_of_surjective _ hbij.2, inertia_subgroup_index, IsGalois.card_aut_eq_finrank,
      hdeg, show n + 1 = (n - 1) + 2 by omega, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardI, hcardD])
  change σ ∈ P.inertia Gal(L/ℚ) ↔ _
  rw [heq]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition
