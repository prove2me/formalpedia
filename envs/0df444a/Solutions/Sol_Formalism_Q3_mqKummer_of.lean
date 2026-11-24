-- Prove2me | solution 1 for Formalism.Q3.mqKummer_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:08.80733+00:00
-- url     : https://prove2.me/submissions/3e5c940e-f729-4fb0-827b-afca6462382f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Theorems.Thm_Formalism_Q3_mqk_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hG : MQGalois) : MQKummer := by
  unfold MQGalois at hG
  unfold MQKummer
  intro k E _ _ a α hα hns
  have hα' := hα
  obtain ⟨hsq, htop⟩ := hα
  have hne : ∀ i, a i ≠ 0 := by
    intro i h0
    apply hns {i} (Finset.singleton_nonempty i)
    rw [Finset.prod_singleton, h0]
    exact ⟨0, by simp⟩
  obtain ⟨hgal, -, -, hinj⟩ := hG k E a α hα' hne
  obtain ⟨hfr0, hsqs⟩ := mqk_induction ℚ a α hsq hns Finset.univ
  have huniv : mqkField ℚ α Finset.univ = ⊤ := by
    rw [← htop]
    simp only [mqkField, Finset.coe_univ, Set.image_univ]
  have hfr : Module.finrank ℚ E = 2 ^ k := by
    rw [huniv, IntermediateField.finrank_top'] at hfr0
    simpa using hfr0
  refine ⟨hfr, ?_, ?_⟩
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    have h1 : Fintype.card Gal(E/ℚ) = 2 ^ k := by
      rw [← hfr]
      first
      | (rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank (F := ℚ) (E := E))
      | (convert IsGalois.card_aut_eq_finrank (F := ℚ) (E := E) using 1)
    rw [h1]
    simp [Fintype.card_units_int]
  · intro d
    constructor
    · rintro ⟨r, hr⟩
      have hr2 : r ^ 2 = algebraMap ℚ E d := by rw [hr, sq]
      obtain ⟨S, -, hS⟩ := hsqs d r (by rw [huniv]; exact IntermediateField.mem_top) hr2
      exact ⟨S, hS⟩
    · rintro ⟨S, t, ht⟩
      have hαne : ∀ i, α i ≠ 0 := by
        intro i h
        have h2 := hsq i
        rw [h, zero_pow two_ne_zero] at h2
        exact hne i (by exact_mod_cast h2.symm)
      set P := ∏ i ∈ S, α i with hP
      have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hαne i
      have hcast : algebraMap ℚ E d * P ^ 2 = algebraMap ℚ E t * algebraMap ℚ E t := by
        have h1 := congrArg (algebraMap ℚ E) ht
        rw [map_mul, map_mul, map_prod] at h1
        rw [← h1, hP, ← Finset.prod_pow]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by rw [hsq i]; simp
      refine ⟨algebraMap ℚ E t / P, ?_⟩
      field_simp
      linear_combination hcast
end Formalism.Q3
