-- Prove2me | solution 1 for Formalism.QuantumDeterminants.big_cell_coordinate_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:24.624302+00:00
-- url     : https://prove2.me/submissions/10e4123d-69c2-4a3b-bc16-dd89b862eadf

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mulVec_apply
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_sgn_of_ne
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_lo
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_hi
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_star_bvec_dot
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mulVec_bvec
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_val
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt


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
theorem _root_.solution : BigCellZhat := by
  intro k r z z' c μ hz hz'
  ext a b
  show herm (Hpk k r) (bigCell k r c μ *ᵥ fvec k r z' b) (fvec k r z a) = _
  rw [diagonal_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hb1 : b.val < r
  · set bb : Fin r := ⟨b.val, hb1⟩
    have hf : fvec k r z' b = bvec (eI k r bb) := by unfold fvec; rw [dif_pos hb1]
    rw [hf]
    have hw : ∀ p, (Hpk k r *ᵥ (bigCell k r c μ *ᵥ bvec (eI k r bb))) p =
        if p = eI k r bb then c bb else 0 := by
      intro p
      rw [hpk_mulVec_apply, mulVec_bvec, col_lo c μ _ _ bb rfl]
      by_cases hp : p = eI k r bb
      · subst hp
        rw [if_pos rfl, sgn_of_ne _ (by simp only [eI, bb]; omega),
          if_pos (by rw [sig_lo _ _ _ (by simp [eI])]; simp [eI]), one_mul]
      · rw [if_neg hp, if_neg, mul_zero]
        intro h; apply hp; apply Fin.ext
        have h' : (sig k r p).val = 2 * r + k - b.val := h
        have := sig_val k r p
        show p.val = b.val
        split_ifs at this <;> omega
    rw [herm, dotProduct]
    simp only [hw, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Pi.star_apply, fvec_apply_lt z hz a (eI k r bb) (by show b.val < r; exact hb1)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos (by simp [eI, bb]), dif_pos hb1]
      simp only [star_one, one_mul]
      rfl
    · rw [if_neg hab, if_neg (by simp only [eI, bb]; intro h; exact hab (Fin.ext h)), star_zero, zero_mul]
  · have hbr : b.val = r := by omega
    have hf : fvec k r z' b = z' := by unfold fvec; rw [dif_neg hb1]
    rw [hf]
    by_cases ha1 : a.val < r
    · set aa : Fin r := ⟨a.val, ha1⟩
      have hfa : fvec k r z a = bvec (eI k r aa) := by unfold fvec; rw [dif_pos ha1]
      rw [hfa, if_neg (by intro h; rw [h] at ha1; exact hb1 ha1)]
      rw [herm, star_bvec_dot, hpk_mulVec_apply, sgn_of_ne _ (by simp only [eI, aa]; omega), one_mul, mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      have hs : (sig k r (eI k r aa)).val = 2 * r + k - aa.val := by
        rw [sig_lo _ _ _ (by show a.val < r; exact ha1)]; simp [eI]
      rw [row_hi c μ _ _ aa hs]
      by_cases hq : q.val = aa.val
      · rw [hz' q (Or.inl (by simp only [aa] at hq; omega)), mul_zero]
      · rw [if_neg hq, zero_mul]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      have hfa : fvec k r z a = z := by unfold fvec; rw [dif_neg ha1]
      rw [hfa, if_pos rfl, dif_neg ha1]
end Formalism.QuantumDeterminants
