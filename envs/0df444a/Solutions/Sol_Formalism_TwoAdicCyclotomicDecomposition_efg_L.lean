-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.efg_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:14.439198+00:00
-- url     : https://prove2.me/submissions/5d5a0ad7-a5d2-481b-88b9-6d85a6076291

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_exists_int_quad
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_stab_fix
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_le_inertiaDeg
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_le_ramificationIdx
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_sgn_eq_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime
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
theorem _root_.solution (hG : LayerGalois) {n q d : ℕ} (hn : 1 ≤ n) (hqd : HypQD q d)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 2 ^ (n - 1) ∧ P.inertiaDeg ℤ = 2 ∧
      (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard = 2 := by
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(2 : ℤ)}) (𝓞 L) Gal(L/ℚ)
  rw [ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), IsGalois.card_aut_eq_finrank,
    hdeg] at hfund
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have he := le_ramificationIdx k ζ h.1 P

  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q : ℤ) = 4 * (2 * c + 1) + 1 := ⟨(-(q : ℤ) - 5) / 8, by omega⟩
  have ha : a ^ 2 = ((4 * (2 * c + 1) + 1 : ℤ) : L) := by
    rw [← hc, h.2.1]
    push_cast
    ring
  have hf : 2 ≤ P.inertiaDeg ℤ := by
    have hx2 : ((1 + a) / 2) ^ 2 = (1 + a) / 2 + (((2 * c + 1 : ℤ)) : L) := by
      push_cast at ha ⊢
      linear_combination (1 / 4 : L) * ha
    obtain ⟨W, -, hW⟩ := exists_int_quad _ _ hx2
    exact two_le_inertiaDeg P W _ hW (by omega)

  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  obtain ⟨τ, hτ⟩ := hbij.2 ((1, 1, -1) : GalL (k + 1))
  have hτb : τ b ≠ b := by
    intro hfix
    have : (galMap h.1 a b τ).2.2 = -1 := by rw [hτ]
    change sgn τ b = -1 at this
    rw [(sgn_eq_one_iff τ b).mpr hfix] at this
    exact absurd this (by decide)
  have hτP : τ • P ≠ P := fun heq =>
    hτb (stab_fix b c' hb P τ (MulAction.mem_stabilizer_iff.mpr heq))
  have hne0 : (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfund
    exact absurd hfund.symm (pow_pos two_pos _).ne'
  have hsub : ({P, τ • P} : Set (Ideal (𝓞 L))) ⊆ primesOver (span {(2 : ℤ)}) (𝓞 L) := by
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact ⟨inferInstance, inferInstance⟩
    · rw [Set.mem_singleton_iff] at hQ
      subst hQ
      exact ⟨inferInstance, inferInstance⟩
  have hg : 2 ≤ (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard := by
    rw [← Set.ncard_pair hτP.symm]
    exact Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero hne0)

  set g := (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard
  set e := P.ramificationIdx ℤ
  set f := P.inertiaDeg ℤ
  have hN : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
  rw [hN] at hfund
  simp only [Nat.add_sub_cancel]
  have hef : 2 ^ k * 2 ≤ e * f := Nat.mul_le_mul he hf
  have hef2 : e * f ≤ 2 ^ k * 2 := by nlinarith
  have hef3 : e * f = 2 ^ k * 2 := le_antisymm hef2 hef
  have hpk : 0 < 2 ^ k := by positivity
  have hg2 : g = 2 := by
    rw [hef3] at hfund
    nlinarith
  have he2 : e = 2 ^ k := by
    apply le_antisymm _ he
    nlinarith
  refine ⟨he2, ?_, hg2⟩
  rw [he2] at hef3
  nlinarith
end Formalism.TwoAdicCyclotomicDecomposition
