-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.tw_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:17:20.161307+00:00
-- url     : https://prove2.me/submissions/c32387d0-7b9c-462a-88e9-c1c492c92045

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_LtoR
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_rpow_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_norm_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_right_word_eq_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_rpow_mono_G
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
theorem _root_.solution {A c : ℝ} {m : ℕ} {F : Mat k r → E} (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F)
    (hR : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ GV k r, gN g ^ A * ‖Rw v F g‖ ≤ c)
    (u v : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, unitLie k r X)
    (hl : u.length + v.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GV k r, gN g ^ (A - 2 * (m : ℝ)) * ‖dLR u v F g‖ ≤ C := by
  obtain ⟨L, hL1, hL2⟩ := LtoR (E := E) u hu
  have hH : CkOn ((u.length : ℕ) : ℕ∞) (GV k r) (Rw v F) := by
    rw [right_word_eq_word]
    exact smooth_on_of_word_derivatives _ (allLie_lr' (by simp) fun X hX => (hv X hX).1) _
      (ckOn_mono (by simp [length_lr]; omega) hF)
  have hexC : ∀ p : (Mat k r → ℂ) × List (Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (PolyClass (2 * u.length) p.1 → ∀ g ∈ GV k r, ‖p.1 g‖ ≤ C * gN g ^ (2 * u.length)) := by
    intro p
    by_cases hp : PolyClass (2 * u.length) p.1
    · obtain ⟨C, h0, h⟩ := hp.2 [] (by simp [AllLie])
      exact ⟨C, h0, fun _ g hg => by simpa [W_nil] using h g hg⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose CP hCP0 hCP using hexC
  refine ⟨(L.map fun p => CP p * max c 0).sum,
    list_sum_nonneg _ _ fun p _ => mul_nonneg (hCP0 p) (le_max_right _ _), fun g hg => ?_⟩
  have e : dLR u v F g = (L.map fun p => p.1 g • Rw (p.2 ++ v) F g).sum := by
    rw [show dLR u v F = u.foldr LdV (Rw v F) from rfl, hL2 (Rw v F) hH g hg]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Rw, List.foldr_append]
  rw [e]
  have hgp := gN_pos hg
  have hq : 0 ≤ gN g ^ (A - 2 * (m : ℝ)) := gN_rpow_nonneg g _
  calc gN g ^ (A - 2 * (m : ℝ)) * ‖(L.map fun p => p.1 g • Rw (p.2 ++ v) F g).sum‖
      ≤ gN g ^ (A - 2 * (m : ℝ)) * (L.map fun p => ‖p.1 g • Rw (p.2 ++ v) F g‖).sum :=
        mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hq
    _ = (L.map fun p => gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 g • Rw (p.2 ++ v) F g‖).sum :=
        (list_sum_mul_left _ _ _).symm
    _ ≤ (L.map fun p => CP p * max c 0).sum := by
        refine list_sum_le _ _ _ fun p hp => ?_
        obtain ⟨hpP, hpl, hpu⟩ := hL1 p hp
        have hunit : ∀ X ∈ p.2 ++ v, unitLie k r X := by
          intro X hX
          rcases List.mem_append.1 hX with h | h
          · exact hpu X h
          · exact hv X h
        have hlen : (p.2 ++ v).length ≤ m := by simp; omega
        have hRw := (hR (p.2 ++ v) hunit hlen g hg).trans (le_max_left c 0)
        have hP := hCP p hpP g hg
        have hpow : gN g ^ (A - 2 * (m : ℝ)) * gN g ^ (2 * u.length) ≤ gN g ^ A := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hgp]
          apply rpow_mono_G hg
          have : ((2 * u.length : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
            have h2 : 2 * u.length ≤ 2 * m := by omega
            exact_mod_cast h2
          linarith
        have hnR := norm_nonneg (Rw (p.2 ++ v) F g)
        have hpw : 0 ≤ gN g ^ (2 * u.length) := pow_nonneg hgp.le _
        rw [norm_smul]
        calc gN g ^ (A - 2 * (m : ℝ)) * (‖p.1 g‖ * ‖Rw (p.2 ++ v) F g‖)
            ≤ gN g ^ (A - 2 * (m : ℝ)) * ((CP p * gN g ^ (2 * u.length)) * ‖Rw (p.2 ++ v) F g‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP hnR) hq
          _ = CP p * ((gN g ^ (A - 2 * (m : ℝ)) * gN g ^ (2 * u.length)) * ‖Rw (p.2 ++ v) F g‖) := by ring
          _ ≤ CP p * (gN g ^ A * ‖Rw (p.2 ++ v) F g‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hnR) (hCP0 p)
          _ ≤ CP p * max c 0 := mul_le_mul_of_nonneg_left hRw (hCP0 p)
end Formalism.FourierDecayAlt.P.LeftToRightConversion
