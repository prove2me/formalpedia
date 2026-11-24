-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_coeffT_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:13.407432+00:00
-- url     : https://prove2.me/submissions/55315258-f04a-46eb-a7f8-3eecfedf6a34

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_sum
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_C_monomial_mul
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_iota
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_tau_iota
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_Phi_nil
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_Phi_append_single
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_applyWord_append_single
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_applyWord_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hL : (L.map (·.2.2)).Nodup) (F : MvPolynomial (Fin r × Fin n) R) (d : Fin r × Fin n →₀ ℕ) :
    cwl_coeffT d (cwl_Phi L (cwl_iota F)) =
      if (∀ u, u ∉ L.map (·.2.2) → d u = 0) then
        applyWord R (L.map fun l => (l.1, l.2.1, d l.2.2)) F else 0 := by
  classical
  induction L using List.reverseRecOn generalizing F d with
  | nil =>
    rw [cwl_Phi_nil, cwl_coeffT_iota]
    have : (∀ u, u ∉ ([] : List (Fin r × Fin r × (Fin r × Fin n))).map (·.2.2) → d u = 0) ↔ d = 0 := by
      simp [Finsupp.ext_iff]
    simp only [this]
    rfl
  | append_singleton w l ih =>
    obtain ⟨s, a, v⟩ := l
    have hL' : (w.map (·.2.2) ++ [v]).Nodup := by simpa using hL
    have hw : (w.map (·.2.2)).Nodup := hL'.sublist (List.sublist_append_left _ _)
    have hv : v ∉ w.map (·.2.2) := by
      rw [List.nodup_append] at hL'
      intro h
      exact hL'.2.2 v h v (by simp) rfl
    rw [cwl_Phi_append_single, cwl_tau_iota, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      map_sum, cwl_coeffT_sum]
    have key : ∀ (j : ℕ) (c : MvPolynomial (Fin r × Fin n) R),
        cwl_coeffT d (cwl_Phi w (cwl_iota c * C (X (s, a, v).2.2) ^ j)) =
          if j ≤ d v then cwl_coeffT (d - Finsupp.single v j) (cwl_Phi w (cwl_iota c)) else 0 := by
      intro j c
      have hC : cwl_Phi w (C (X v ^ j) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) =
          C (X v ^ j) := (cwl_Phi w).commutes (X v ^ j)
      have hp : (C (X v) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) ^ j = C (X v ^ j) :=
        (C.map_pow _ _).symm
      simp only
      rw [hp, map_mul, hC, mul_comm, X_pow_eq_monomial, cwl_coeffT_C_monomial_mul]
      simp only [Finsupp.single_le_iff]
    simp only [key, ih hw]
    rw [Finset.sum_eq_single (d v)]
    · simp only [le_refl, if_true]
      have hfill : w.map (fun l => (l.1, l.2.1, (d - Finsupp.single v (d v)) l.2.2)) =
          w.map (fun l => (l.1, l.2.1, d l.2.2)) := by
        apply List.map_congr_left
        intro l hl
        have hne : l.2.2 ≠ v := by
          intro h; exact hv (List.mem_map.mpr ⟨l, hl, h⟩)
        simp [Ne.symm hne]
      have hcond : (∀ u, u ∉ w.map (·.2.2) → (d - Finsupp.single v (d v)) u = 0) ↔
          (∀ u, u ∉ (w ++ [(s, a, v)]).map (·.2.2) → d u = 0) := by
        constructor
        · intro h u hu
          simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton,
            not_or] at hu
          have := h u hu.1
          simpa [Finsupp.single_apply, Ne.symm hu.2] using this
        · intro h u hu
          by_cases huv : u = v
          · subst huv; simp
          · have := h u (by simp [hu, huv])
            simp [this]
      rw [hfill]
      simp only [hcond]
      split_ifs
      · rw [List.map_append, List.map_cons, List.map_nil, cwl_applyWord_append_single]
        rfl
      · rfl
    · intro j _ hj
      split_ifs with h1 h2
      · exfalso
        have := h2 v hv
        simp at this
        omega
      · rfl
      · rfl
    · intro hnot
      rw [Polynomial.notMem_support_iff.mp hnot]
      simp [cwl_applyWord_zero]
end Formalism.L2.G.Model.TS
