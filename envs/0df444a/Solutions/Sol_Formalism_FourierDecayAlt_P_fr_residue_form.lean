-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fr_residue_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.968674+00:00
-- url     : https://prove2.me/submissions/7497876c-656b-4305-98f2-09e51a85e74c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_eU_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Kw_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_letterSum_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ofWord_cons_plus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mem_inv_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ne_of_mem_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Adm_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ins_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_io_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_io_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Kw_nil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.Fr11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.ResidueForm := by
  intro hFA hEC A S _ _ _ _ _ _ r L st J _ Z γ w hL hst
  induction w with
  | nil =>
    intro _ _ hee _ Y _ _ _
    have e1 : (ofWord L st ([] : List (Letter ℂ S))).ee Y = io (st.ee Y) := rfl
    rw [e1, hee Y, Kw_nil, Finset.mul_sum, io_sum]
    simp only [letterSum, mult_nil, mul_one, zero_add, sub_zero, mul_smul_comm, io_smul]
  | cons l w ih =>
    intro hA hp hee hγ Y hY hY1 hYγ
    have hAw := Adm_tail st l w hA
    have hpw : ∀ l' ∈ w, l'.plus = true := fun l' hl => hp l' (by simp [hl])
    have hγw : ∀ l' ∈ w, ∀ j, l'.pt ≠ γ j := fun l' hl => hγ l' (by simp [hl])
    have ih' := ih hAw hpw hee hγw
    have hc := ofWord_cons_plus L st l w (hp l (by simp))
    rw [hc] at hY hY1 ⊢
    obtain ⟨hs, _, hi, hpw2⟩ := hA
    have hpair := (List.pairwise_cons.1 hpw2).1
    have hli := hi l (by simp)

    have hYa : l.pt ∈ (ofWord L st w).inv := by
      refine mem_inv_of L st _ hli.1 w hpw fun l' hl => ⟨?_, ?_⟩
      · simpa using hpair l' hl 0 (by simp)
      · simpa using hpair l' hl 1 (by simp)
    have hYa1 : l.pt + 1 ∈ (ofWord L st w).inv := by
      refine mem_inv_of L st _ hli.2.1 w hpw fun l' hl => ⟨?_, ?_⟩
      · intro h0
        apply hpair l' hl (-1) (by simp)
        push_cast
        linear_combination h0
      · intro h0
        apply hpair l' hl 0 (by simp)
        push_cast
        linear_combination h0
    have hne : Y ≠ l.pt := sub_ne_zero.1 hY.2.1
    have hfr := hFA A S r L st w hL hst hAw
    have hconj := hEC A S r L (ofWord L st w) Y l.pt hfr hY.1 hY1.1 hYa hYa1 hne
    have hEY := ih' Y hY.1 hY1.1 hYγ
    have hEa := ih' l.pt hYa hYa1 (hγ l (by simp))
    have hYw := ne_of_mem_inv L st Y w hpw hY.1
    have hposition : ∀ l' ∈ w, l.intersection_update_fsHerm_neg_one ≠ l'.intersection_update_fsHerm_neg_one := by
      rw [List.map_cons] at hs
      intro l' hl he
      exact (List.nodup_cons.1 hs).1 (he ▸ List.mem_map_of_mem hl)
    have hls := letterSum_step (A := A) l Y hne w [] fun l' hl =>
      ⟨hposition l' hl, hYw l' hl, fun he => by simpa [he] using hpair l' hl 0 (by simp)⟩

    have e1 : ((ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt).ee Y =
        Ph (eU l.intersection_update_fsHerm_neg_one 0 0) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹ ((ofWord L st w).ee Y) ((ofWord L st w).ee l.pt) +
          eU l.intersection_update_fsHerm_neg_one 0 0 * tz L - (Y - l.pt)⁻¹ • eU l.intersection_update_fsHerm_neg_one 0 1 := by
      have e2 : ((ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt).ee Y =
        ins l.intersection_update_fsHerm_neg_one !![(ofWord L st w).ee Y - (ofWord L st w).DD Y l.pt + tz L, -((Y - l.pt)⁻¹ • 1); 0,
          (ofWord L st w).xi l.pt * (ofWord L st w).ee Y * (ofWord L st w).x l.pt] := rfl
      rw [e2, ins_upper, eq_add_of_sub_eq hconj, Ph, FrameData.DD]
      simp only [mul_add, mul_neg, mul_smul_comm, mul_one]
      abel
    rw [e1, hEY, hEa, Ph_sub, Ph_add, Ph_const _ _ _ (eU_sum l.intersection_update_fsHerm_neg_one), Ph_sum, hls, Kw_cons]
    have e3 : ∀ j, Ph (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹
        ((Y - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult w (γ j)))
        ((l.pt - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult w (γ j))) =
        (Y - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult (l :: w) (γ j)) := by
      intro j
      rw [Ph_res _ _ _ _ _ _ (hYγ j) (hγ l (by simp) j) hne, ← mult_single, ← mul_assoc, mult_eq [l], dg_io,
        ← mult_eq, mul_assoc, ← mult_cons]
    simp only [e3, letterSum, mult_nil, mul_one, List.nil_append]
    abel
end Formalism.FourierDecayAlt.P
