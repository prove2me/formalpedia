-- Prove2me | solution 1 for Formalism.Q3.hostConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:12.151814+00:00
-- url     : https://prove2.me/submissions/c834d2b0-9d1d-4428-b606-d1f8c0cea320

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_alpha_sq
import Theorems.Thm_Formalism_Q3_CMConjugation_galSign_eq_cc_iff
import Theorems.Thm_Formalism_Q3_CMConjugation_phi_conj
import Theorems.Thm_Formalism_Q3_CMConjugation_phi_alpha_ne_zero
import Theorems.Thm_Formalism_Q3_CMConjugation_part1
import Theorems.Thm_Formalism_Q3_CMConjugation_not_sq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open CMConjugation
namespace Formalism.Q3
theorem _root_.solution (hH : HostGalois) (hK : MQKummer) : HostConj := by
  intro q hq E _ _ α hα
  obtain ⟨hGal, hfin, hbij, _hmul⟩ := hH q hq E α hα
  have h1 : ∀ (φ : E →+* ℂ) (σ : Gal(E/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galSign α σ = cc := part1 hq hα
  obtain ⟨σc, hσc⟩ := hbij.2 cc
  have hTC : IsTotallyComplex E := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h2 := RingHom.congr_fun h (α 0)
    rw [ComplexEmbedding.conjugate_coe_eq, phi_conj hq hα] at h2
    have h3 : (2 : ℂ) * w.embedding (α 0) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact phi_alpha_ne_zero hq hα _ 0 h4
  have hCM : IsCMField E := by
    refine IsCMField.of_forall_isConj E (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact ((h1 φ σc).2 hσc x).symm
  have h5 : ∀ x : E, x ∈ maximalRealSubfield E ↔ ∀ σ : Gal(E/ℚ), galSign α σ = cc → σ x = x := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx σ hσ
      let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
      apply φ.injective
      rw [(h1 φ σ).2 hσ x]
      exact hx φ
    · intro h φ
      have := (h1 φ σc).2 hσc x
      rw [h σc hσc] at this
      exact this.symm
  have h4 : Module.finrank ℚ (maximalRealSubfield E) = 4 := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hfin] at h
    omega
  refine ⟨h1, hCM, ?_, h4, h5, ?_⟩
  · intro _
    let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply (h1 φ _).1
    intro x
    rw [AlgEquiv.restrictScalars_apply, IsCMField.complexEmbedding_complexConj]
  · have hcc : ∀ σ : Gal(E/ℚ), galSign α σ = cc → ∀ i, σ (α i) = -α i :=
      fun σ hσ => (galSign_eq_cc_iff hq hα σ).1 hσ
    set K := IntermediateField.adjoin ℚ ({α 0 * α 1, α 1 * α 2} : Set E) with hKdef
    let L : IntermediateField ℚ E := (maximalRealSubfield E).toIntermediateField
      (fun r => (h5 _).2 (fun σ _ => σ.commutes r))
    have hKL : K ≤ L := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      show x ∈ maximalRealSubfield E
      rw [h5]
      intro σ hσ
      rcases hx with rfl | rfl
      · rw [map_mul, hcc σ hσ, hcc σ hσ]; ring
      · rw [map_mul, hcc σ hσ, hcc σ hσ]; ring
    have hp := fun i => (hq.1 i).1
    have hndvd : ∀ i j, i ≠ j → ¬ q i ∣ q j := fun i j hij h =>
      hq.2.ne hij ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).1 h)
    have key : ∀ n : ℕ, ¬ IsSquare n → ¬ IsSquare (n : ℚ) := fun n h => by
      rwa [Rat.isSquare_natCast_iff]
    have hKfin : Module.finrank ℚ K = 4 := by
      let β : Fin 2 → K := ![⟨α 0 * α 1, IntermediateField.subset_adjoin ℚ _ (by simp)⟩,
        ⟨α 1 * α 2, IntermediateField.subset_adjoin ℚ _ (by simp)⟩]
      let a : Fin 2 → ℤ := ![((q 0 * q 1 : ℕ) : ℤ), ((q 1 * q 2 : ℕ) : ℤ)]
      have hmq' : @IsMQ 2 K _ K.algebra' a β := by
        refine ⟨?_, ?_⟩
        · intro i
          apply Subtype.ext
          fin_cases i
          · simp [β, a, mul_pow, alpha_sq hα]
          · simp [β, a, mul_pow, alpha_sq hα]
        · apply IntermediateField.map_injective K.val
          rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
            IntermediateField.fieldRange_val]
          show _ = IntermediateField.adjoin ℚ ({α 0 * α 1, α 1 * α 2} : Set E)
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
            fin_cases i
            · left; rfl
            · right; rfl
          · rintro (rfl | rfl)
            · exact ⟨β 0, ⟨0, rfl⟩, rfl⟩
            · exact ⟨β 1, ⟨1, rfl⟩, rfl⟩
      have hmq : IsMQ a β := by convert hmq'; exact Subsingleton.elim _ _
      have hns : ∀ S : Finset (Fin 2), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : ℚ)) := by
        intro S hS
        have hS' : S = {0} ∨ S = {1} ∨ S = Finset.univ := by
          revert S; decide
        rcases hS' with rfl | rfl | rfl
        · have e : (∏ i ∈ ({0} : Finset (Fin 2)), (a i : ℚ)) = ((q 0 * q 1 : ℕ) : ℚ) := by
            simp [a]
          rw [e]; exact key _ (not_sq_mul _ _ (hp 0) (hndvd 0 1 (by decide)))
        · have e : (∏ i ∈ ({1} : Finset (Fin 2)), (a i : ℚ)) = ((q 1 * q 2 : ℕ) : ℚ) := by
            simp [a]
          rw [e]; exact key _ (not_sq_mul _ _ (hp 1) (hndvd 1 2 (by decide)))
        · have e : (∏ i ∈ (Finset.univ : Finset (Fin 2)), (a i : ℚ)) =
              ((q 0 * (q 1 * q 1 * q 2) : ℕ) : ℚ) := by
            simp [a, Fin.prod_univ_two]; ring
          rw [e]
          refine key _ (not_sq_mul _ _ (hp 0) ?_)
          intro h
          rcases (hp 0).dvd_mul.1 h with h | h
          · rcases (hp 0).dvd_mul.1 h with h | h
            · exact hndvd 0 1 (by decide) h
            · exact hndvd 0 1 (by decide) h
          · exact hndvd 0 2 (by decide) h
      have := (hK 2 K a β hmq hns).1
      convert this using 1
      norm_num
    have hLfin : Module.finrank ℚ L = 4 := h4
    have hKL' := IntermediateField.eq_of_le_of_finrank_eq hKL (hKfin.trans hLfin.symm)
    rw [hKL']
    rfl
end Formalism.Q3
