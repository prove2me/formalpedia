-- Prove2me | solution 1 for Formalism.QuantumDeterminants.big_cell_mem_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:22:51.49944+00:00
-- url     : https://prove2.me/submissions/51e6a8e7-63bd-4878-b1b5-e5443858f289

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_sgn_of_ne
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_lo
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_hi
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_mid
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_lo
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_hi
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_mid_out
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mid_mid
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_sum_mid
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open GBasic BruhatBigCell
namespace Formalism.QuantumDeterminants
theorem _root_.solution : BigCellMem := by
  intro k r c μ hc hμ
  show (bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, mul_apply]
  simp only [conjTranspose_apply, hpk_mul_apply']
  have hi := i.isLt
  have hj := j.isLt
  rw [Hpk_eq]
  by_cases h1 : i.val < r
  ·
    set a : Fin r := ⟨i.val, h1⟩
    rw [Finset.sum_eq_single (esI k r a)]
    · have hs : (sig k r (esI k r a)).val = a.val := by
        rw [sig_hi _ _ _ (by simp only [esI, a]; omega)]; simp only [esI, a]; omega
      rw [col_lo c μ _ _ a rfl, if_pos (by simp [esI]), row_lo c μ _ _ a hs,
        sgn_of_ne _ (by simp only [esI, a]; omega), sgn_of_ne _ (by omega)]
      have e : (j = sig k r i) ↔ j.val = 2 * r + k - a.val := by
        rw [Fin.ext_iff, sig_lo _ _ _ h1]
      by_cases h : j.val = 2 * r + k - a.val
      · rw [if_pos h, if_pos (e.2 h), one_mul]
        have : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
        field_simp
      · rw [if_neg h, if_neg (fun h' => h (e.1 h')), mul_zero, mul_zero]
    · intro p _ hp
      rw [col_lo c μ _ _ a rfl, if_neg, star_zero, zero_mul]
      intro h; exact hp (Fin.ext (by simp only [esI, a]; omega))
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases h2 : i.val ≤ r + k
    ·
      set q0 : Fin (k + 1) := ⟨i.val - r, by omega⟩
      have hi0 : i = wI k r q0 := Fin.ext (by simp only [wI, q0]; omega)
      rw [sum_mid]
      swap
      · intro p hp
        rw [col_mid c μ _ _ (by omega) h2, dif_neg (by omega), star_zero, zero_mul]
      have hsig : ∀ q : Fin (k + 1), sig k r (wI k r q) = wI k r q := fun q =>
        sig_mid _ _ _ (by simp [wI]) (by simp only [wI]; omega)
      simp only [hsig]
      rw [sig_mid _ _ _ (by omega) h2, hi0]
      simp only [mid_mid]
      by_cases h3 : r ≤ j.val ∧ j.val ≤ r + k
      · set q1 : Fin (k + 1) := ⟨j.val - r, by omega⟩
        have hj1 : j = wI k r q1 := Fin.ext (by simp only [wI, q1]; omega)
        rw [hj1]
        simp only [mid_mid]
        have key := congrFun (congrFun hμ q0) q1
        rw [Matrix.mul_assoc, mul_apply] at key
        simp only [Hb, diagonal_mul, conjTranspose_apply] at key
        have hsg : ∀ q : Fin (k + 1), sgn k r (wI k r q) = (if q = Fin.last k then -1 else 1) := by
          intro q
          have hq : ((wI k r q).val = r + k) ↔ q = Fin.last k := by
            simp only [wI, Fin.ext_iff, Fin.val_last]; constructor <;> intro h <;> omega
          unfold sgn; simp only [hq]
        simp only [hsg]
        rw [show (∑ x : Fin (k + 1), star (μ x q0) * ((if x = Fin.last k then -1 else 1) * μ x q1)) =
            ∑ x : Fin (k + 1), star (μ x q0) * ((if x = Fin.last k then -1 else 1) * μ x q1) from rfl, key]
        simp only [diagonal_apply]
        have e : (wI k r q1 = wI k r q0) ↔ q0 = q1 := by
          simp only [wI, Fin.ext_iff]; constructor <;> intro h <;> omega
        by_cases h4 : q0 = q1
        · rw [if_pos h4, if_pos (e.2 h4)]
        · rw [if_neg h4, if_neg (fun h => h4 (e.1 h))]
      · rw [if_neg]
        · apply Finset.sum_eq_zero
          intro q _
          rw [row_mid_out c μ _ _ (by simp [wI]) (by simp only [wI]; omega) (by omega),
            mul_zero, mul_zero]
        · intro h; apply h3; rw [h]; simp only [wI, q0]; omega
    ·
      set a : Fin r := ⟨2 * r + k - i.val, by omega⟩
      have hia : i.val = 2 * r + k - a.val := by simp only [a]; omega
      rw [Finset.sum_eq_single (eI k r a)]
      · have hs : (sig k r (eI k r a)).val = 2 * r + k - a.val := by
          rw [sig_lo _ _ _ (by simp [eI])]; simp [eI]
        rw [col_hi c μ _ _ a hia, if_pos (by simp [eI]), row_hi c μ _ _ a hs,
          sgn_of_ne _ (by simp only [eI]; omega), sgn_of_ne _ (by omega)]
        have e : (j = sig k r i) ↔ j.val = a.val := by
          rw [Fin.ext_iff, sig_hi _ _ _ (by omega)]
        by_cases h : j.val = a.val
        · rw [if_pos h, if_pos (e.2 h), one_mul, star_inv₀, star_star]
          exact inv_mul_cancel₀ (hc a)
        · rw [if_neg h, if_neg (fun h' => h (e.1 h')), mul_zero, mul_zero]
      · intro p _ hp
        rw [col_hi c μ _ _ a hia, if_neg, star_zero, zero_mul]
        intro h; exact hp (Fin.ext (by simp only [eI]; omega))
      · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.QuantumDeterminants
