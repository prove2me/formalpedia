-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mono_not_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:47.214154+00:00
-- url     : https://prove2.me/submissions/f0a3c826-bae7-4949-b453-b209042b75d0

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_uniChar_val
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_elM_isUT
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_elM_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mul_elM
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_edgeSum_elM
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (n : GL (Fin N) K)
    (π : Equiv.Perm (Fin N)) (t : Fin N → K) (ht : ∀ j, t j ≠ 0)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : ¬ MonoAdm π t) :
    ∃ u u' : uniSub K N, (u : GL (Fin N) K) * n * u' = n ∧
      uniChar ψ₀ N u * uniChar ψ₀ N u' ≠ 1 := by
  unfold MonoAdm at hadm
  push Not at hadm
  obtain ⟨i, j, hij, hlt, hbad⟩ := hadm
  obtain ⟨a0, ha0⟩ := (AddChar.ne_one_iff).mp hψ
  have hilt : i < j := by show (i : ℕ) < j; omega
  set s : K := if (π j : ℕ) = π i + 1 then t i / t j else 0 with hs
  have hs1 : 1 - s ≠ 0 := by
    rw [hs]
    split_ifs with h
    · have := hbad h
      intro h'
      apply this
      have h'' : t i / t j = 1 := (sub_eq_zero.mp h').symm
      rwa [div_eq_one_iff_eq (ht j)] at h''
    · simp
  set a : K := a0 / (1 - s) with ha
  set c0 : K := a * t i / t j with hc0
  refine ⟨⟨utMk _ (elM_isUT (π i) (π j) (-c0) hlt), elM_isUT (π i) (π j) (-c0) hlt⟩,
    ⟨utMk _ (elM_isUT i j a hilt), elM_isUT i j a hilt⟩, ?_, ?_⟩
  · apply Units.ext
    ext x c
    simp only [Units.val_mul, utMk_val]
    rw [mul_elM, elM_mul, elM_mul, hn, hn, hn, hn]
    have hne : π j ≠ π i := ne_of_gt hlt
    rw [if_neg hne]
    by_cases hx : x = π i
    · by_cases hc : c = j
      · rw [if_pos hx, if_pos hc, hc, if_pos rfl, if_pos hx]
        rw [hx, if_neg hne.symm, hc0]
        have htj := ht j
        simp only [if_true, mul_zero, add_zero, zero_add]
        field_simp
        ring
      · have : π j ≠ π c := fun h' => hc (π.injective h').symm
        rw [if_neg hc, if_neg this]
        simp
    · rw [if_neg hx, if_neg hx]
      simp
  · intro h
    apply ha0
    have h' := congrArg (fun z : ℂˣ => (z : ℂ)) h
    simp only [Units.val_mul, uniChar_val, Units.val_one, utMk_val] at h'
    rw [← AddChar.map_add_eq_mul, edgeSum_elM, edgeSum_elM, if_pos hij] at h'
    have e : (if (π j : ℕ) = π i + 1 then -c0 else 0) + a = a0 := by
      have e1 : (if (π j : ℕ) = π i + 1 then -c0 else 0) = - (a * s) := by
        rw [hs]
        split_ifs with h
        · rw [hc0]; ring
        · simp
      rw [e1, ha]
      field_simp
      ring
    rw [e] at h'
    exact h'
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
