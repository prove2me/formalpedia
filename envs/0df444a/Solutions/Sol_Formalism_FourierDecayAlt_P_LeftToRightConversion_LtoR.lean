-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.LtoR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:02.456907+00:00
-- url     : https://prove2.me/submissions/0caef786-02a7-49e8-9231-3626d5eff371

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_L_to_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_polyClass_cT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_listSumF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_smulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_top_nat
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_right_word_eq_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
theorem _root_.solution : ∀ u : List (Mat k r), (∀ X ∈ u, inLie k r X) →
    ∃ L : List ((Mat k r → ℂ) × List (Mat k r)),
      (∀ p ∈ L, PolyClass (2 * u.length) p.1 ∧ p.2.length ≤ u.length ∧ ∀ Y ∈ p.2, unitLie k r Y) ∧
      ∀ H : Mat k r → E, CkOn ((u.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
        u.foldr LdV H g = (L.map fun p => p.1 g • Rw p.2 H g).sum := by
  intro u
  induction u with
  | nil =>
    intro _
    refine ⟨[(fun _ => 1, [])], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨polyClass_const 1, le_rfl, by simp⟩
    · intro H _ g _
      simp [Rw]
  | cons Y u ih =>
    intro hu
    have hY : inLie k r Y := hu Y List.mem_cons_self
    obtain ⟨L', hL'1, hL'2⟩ := ih fun X hX => hu X (List.mem_cons_of_mem _ hX)
    refine ⟨L'.flatMap fun p => (op true Y p.1, p.2) ::
      ((Finset.univ.toList : List (J k r)).map fun i => ((fun g => p.1 g * cT i Y g), Lt i :: p.2)), ?_, ?_⟩
    · intro q hq
      rw [List.mem_flatMap] at hq
      obtain ⟨p, hp, hq⟩ := hq
      obtain ⟨hp1, hp2, hp3⟩ := hL'1 p hp
      rcases List.mem_cons.1 hq with h | h
      · subst h
        refine ⟨polyClass_mono (by rw [List.length_cons]; omega) (polyClass_op hp1 true hY),
          by show p.2.length ≤ (Y :: u).length; rw [List.length_cons]; omega, hp3⟩
      · rw [List.mem_map] at h
        obtain ⟨i, -, rfl⟩ := h
        refine ⟨?_, by show (Lt i :: p.2).length ≤ (Y :: u).length; rw [List.length_cons, List.length_cons]; omega, ?_⟩
        · have := polyClass_mul hp1 (polyClass_cT i Y)
          rwa [show 2 * u.length + 2 = 2 * (Y :: u).length by rw [List.length_cons]; ring] at this
        · intro Z hZ
          rcases List.mem_cons.1 hZ with h | h
          · rw [h]; exact Lt_unit i
          · exact hp3 Z h
    · intro H hH g hg
      have hH' : CkOn ((u.length : ℕ) : ℕ∞) (GV k r) H := ckOn_mono (by simp) hH
      have hC1 : ∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.1 := fun p hp => ckOn_top_nat (hL'1 p hp).1.1 1
      have hC2 : ∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Rw p.2 H) := by
        intro p hp
        obtain ⟨-, hp2, hp3⟩ := hL'1 p hp
        rw [right_word_eq_word]
        exact smooth_on_of_word_derivatives _ (allLie_lr' (by simp) fun X hX => (hp3 X hX).1) 1
          (ckOn_mono (by simp [length_lr]; omega) hH)
      show op true Y (u.foldr LdV H) g = _
      rw [op_congr true hY (hL'2 H hH') g hg]
      rw [op_listSumF hY (fun p g' => p.1 g' • Rw p.2 H g') L'
        (fun p hp => ckOn_mulF (f := p.1) (H := Rw p.2 H) (hC1 p hp) (hC2 p hp)) g hg]
      rw [list_sum_flatMap]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      rw [op_smulF true hY (hC1 p hp) (hC2 p hp) hg, L_to_R hY (hC2 p hp) hg]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      congr 1
      rw [Finset.sum_map_toList, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      rfl
end Formalism.FourierDecayAlt.P.LeftToRightConversion
