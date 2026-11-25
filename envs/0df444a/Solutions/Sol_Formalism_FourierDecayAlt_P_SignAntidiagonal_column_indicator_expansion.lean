-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:23:07.624297+00:00
-- url     : https://prove2.me/submissions/e73f481d-5cc9-43f3-b91d-d4073821b544

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sign_alternates_add_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_AAx_head
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_derivative_leading_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_bvec_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_la_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_second_peeling_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgnW_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_strictMono_snoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sum_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sum_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_third_polynomial_expansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : ExpansionCovector := by
  intro A _ _ M _ _ k r z' yb E La xi i0 s h t u hs hj hR hh ht hz' hyb hzy hxa hxi0
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef
  set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun l => xR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef
  have hfv : ∀ l, (f l).val = (i.succAbove l).val := by intro l; simp [f, xR, eI]
  have hf : StrictMono f := by
    intro a b hab; show (f a).val < (f b).val; rw [hfv, hfv]; exact Fin.strictMono_succAbove _ hab
  set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef
  have hew : ∀ w, StrictMono (ew w) := by
    intro w
    apply strictMono_snoc f hf
    intro l; show (f l).val < (wI k _ w).val; rw [hfv]; simp [wI]; have := (i.succAbove l).isLt; omega
  have hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _ := by
    intro w j
    constructor
    · intro hj
      by_contra hne
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have := congrArg Fin.val hj
      simp only [ew, Fin.snoc_castSucc] at this
      rw [hfv] at this; simp [wI] at this; have := (i.succAbove l).isLt; omega
    · rintro rfl; simp [ew]

  have hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * (h.det * t ^ s'' * sgnW s'') := by
    intro w
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]
    · simp only [Matrix.of_apply, if_pos rfl, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one,
        Fin.succAbove_last]
      have hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
          else xi (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc =
          Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply]
        rw [if_neg (Fin.succAbove_ne i a)]
        simp only [ew, Fin.snoc_castSucc]
        have hb := (i.succAbove b).isLt
        have hbne : (i.succAbove b).val ≠ i0 := fun h' => Fin.succAbove_ne i b (Fin.ext h')
        have hane : (i.succAbove a).val ≠ i0 := fun h' => Fin.succAbove_ne i a (Fin.ext h')
        rw [hxa _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; exact hbne⟩, hfv]
        simp [i]
      rw [hsub, third_polynomial_expansion]
      simp only [Fin.val_last]
      rw [show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]
      norm_num
    · intro j _ hj
      simp only [Matrix.of_apply, if_pos rfl]
      rw [if_neg (fun h' => hj ((hew_last w j).mp h'))]; simp
    · simp
  have hAA : AAx k (i0 + s'' + 1) E xi (i0 + s'' + 1) le_rfl u =
      ((-1) ^ s'' * (h.det * t ^ s'' * sgnW s'')) • ∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb •
        qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u := by
    unfold AAx
    rw [sum_lin (fun c => StrictMono c) (fun a p => xi (Fin.castLE le_rfl a) p) i
      (fun w => herm (Hpk k _) (bvec (wI k _ w)) yb) (fun w p => if p = wI k _ w then 1 else 0)
      (fun p => by rw [hxi0 _ _ (by simp [i])]; exact herm_bvec_sum k _ yb hyb p)]
    rw [Finset.smul_sum]
    congr 1; ext w
    rw [sum_single (fun c => StrictMono c) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]
    · intro a p hp
      by_cases ha : a = i
      · rw [if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩
      · rw [if_neg ha]
        have hane : a.val ≠ i0 := fun h' => ha (Fin.ext h')
        rw [hxa _ _ (by simpa using hane)]
        rw [if_neg]
        rintro ⟨hp1, hp2⟩
        apply hp
        refine ⟨Fin.castSucc ⟨if p.val < i0 then p.val else p.val - 1, by split_ifs <;> omega⟩, ?_⟩
        ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega
    · intro c hc hS; exact uniq_mono _ _ (hew w) hc hS
  have hhead : AAx k (i0 + s'' + 1) E xi i0 (by omega) u =
      h.det • qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxa _ _ (by omega)]
      split_ifs
      · unfold Zb; rw [dif_pos ha, dif_neg (by omega)]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hxa _ _ (by simp; omega), if_pos (by simp [xR, eI]; omega)]
      unfold Zb
      simp [xR, eI]
  have hP := second_peeling_identity A k (i0 + s'') z' yb E i u hz'
  have hLa : (∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb • La (qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u)) =
      t • La (qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u) := by
    have := la_congr hR hP
    rw [map_sum] at this
    simp only [map_smul] at this
    rw [hzy] at this
    exact this
  have hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s'' := by
    rw [show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]
  rw [hAA, hhead, map_smul, map_smul, map_sum]
  simp only [map_smul]
  rw [hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show s'' + 2 - 1 = s'' + 1 by omega]
  rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h1 | h1 <;> rw [h1] <;> field_simp <;> ring
end Formalism.FourierDecayAlt.P.SignAntidiagonal
