-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:33.255002+00:00
-- url     : https://prove2.me/submissions/683df9c7-0b36-4952-b0cb-d2536a418543

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_rowOp_isUT
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_rowOp_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_colOp_isUT
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mul_colOp
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
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (g : GL (Fin N) K) : ∀ k : ℕ, k ≤ N → ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ p, Cleared ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) k p := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, ?_, id, ?_⟩
    · rw [Units.val_one]; exact IsUT.one
    · rw [Units.val_one]; exact IsUT.one
    · intro j hj; omega
  | succ k ih =>
    intro hk
    obtain ⟨u, u', hu, hu', p, hp⟩ := ih (by omega)
    set hh : GL (Fin N) K := u * g * u' with hhdef
    set h : Matrix (Fin N) (Fin N) K := (hh : Matrix (Fin N) (Fin N) K) with hdef
    set kk : Fin N := ⟨k, by omega⟩ with hkk
    have hex : ∃ r, h r kk ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : h.det = 0 := Matrix.det_eq_zero_of_column_eq_zero kk hcon
      have h1 : IsUnit h.det := (Matrix.isUnit_iff_isUnit_det _).mp hh.isUnit
      exact h1.ne_zero h0
    set S : Finset (Fin N) := Finset.univ.filter (fun r => h r kk ≠ 0) with hS
    have hSne : S.Nonempty := by
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    set r0 := S.max' hSne with hr0
    have hd : h r0 kk ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    have hmax : ∀ i, r0 < i → h i kk = 0 := by
      intro i hi
      by_contra hne
      have := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact absurd hi (not_lt.mpr this)
    set d := h r0 kk with hddef
    set a : Fin N → K := fun i => if i < r0 then - h i kk / d else 0 with hadef
    set b : Fin N → K := fun c => if kk < c then - h r0 c / d else 0 with hbdef
    have haUT : IsUT (rowOp a r0) := rowOp_isUT a r0 (fun i hi => by
      simp only [hadef]; rw [if_neg (not_lt.mpr hi)])
    have hbUT : IsUT (colOp kk b) := colOp_isUT kk b (fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)])
    refine ⟨utMk _ haUT * u, u' * utMk _ hbUT, ?_, ?_, Function.update p kk r0, ?_⟩
    · rw [Units.val_mul]; exact IsUT.mul haUT hu
    · rw [Units.val_mul]; exact IsUT.mul hu' hbUT
    have hprod : ((utMk _ haUT * u * g * (u' * utMk _ hbUT) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = rowOp a r0 * h * colOp kk b := by
      have : utMk _ haUT * u * g * (u' * utMk _ hbUT) = utMk _ haUT * hh * utMk _ hbUT := by
        rw [hhdef]; group
      rw [this, Units.val_mul, Units.val_mul, utMk_val, utMk_val]
    rw [hprod]
    have hform : ∀ i c, (rowOp a r0 * h * colOp kk b) i c =
        h i c + a i * h r0 c + (h i kk + a i * d) * b c := by
      intro i c
      rw [mul_colOp, rowOp_mul, rowOp_mul]
    have F1 : ∀ j : Fin N, (j : ℕ) < k → p j ≠ r0 := by
      intro j hj h'
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      have := (hp j hj).2.2 kk hne
      rw [h'] at this
      exact hd this
    have F2 : ∀ j : Fin N, (j : ℕ) < k → h r0 j = 0 := fun j hj =>
      (hp j hj).2.1 r0 (F1 j hj).symm
    have F3 : ∀ i, h i kk + a i * d = if i = r0 then d else 0 := by
      intro i
      rcases lt_trichotomy i r0 with h1 | h1 | h1
      · simp only [hadef]
        rw [if_pos h1, if_neg (ne_of_lt h1)]
        field_simp
        ring
      · simp only [hadef]
        rw [if_pos h1, h1, if_neg (lt_irrefl _), zero_mul, add_zero]
      · simp only [hadef]
        rw [if_neg (ne_of_gt h1), if_neg (not_lt.mpr h1.le), hmax i h1, zero_mul, add_zero]
    have F4 : ∀ j : Fin N, (j : ℕ) < k → a (p j) = 0 := by
      intro j hj
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      simp only [hadef]
      rw [(hp j hj).2.2 kk hne]
      simp
    have F5 : ∀ c, c ≤ kk → b c = 0 := fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)]
    have F6 : a r0 = 0 := by simp only [hadef]; rw [if_neg (lt_irrefl _)]
    intro j hj
    by_cases hjk : j = kk
    · rw [hjk, Function.update_self]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F6, F5 kk le_rfl]
        simpa using hd
      · intro i hi
        rw [hform, F5 kk le_rfl, mul_zero, add_zero, F3, if_neg hi]
      · intro c hc
        rw [hform, F6, zero_mul, zero_mul, add_zero, add_zero]
        rcases lt_or_gt_of_ne hc with h1 | h1
        · rw [F5 c h1.le, mul_zero, add_zero]
          exact F2 c h1
        · simp only [hbdef]
          rw [if_pos h1]
          field_simp
          ring
    · have hjlt : (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
        omega
      have hjle : j ≤ kk := by show (j : ℕ) ≤ k; omega
      rw [Function.update_of_ne hjk]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F5 j hjle, F4 j hjlt]
        simpa using (hp j hjlt).1
      · intro i hi
        rw [hform, F5 j hjle, F2 j hjlt, (hp j hjlt).2.1 i hi]
        simp
      · intro c hc
        rw [hform, F3, if_neg (F1 j hjlt), F4 j hjlt, (hp j hjlt).2.2 c hc]
        simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
