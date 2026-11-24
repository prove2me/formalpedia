-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:49.521091+00:00
-- url     : https://prove2.me/submissions/5a60cd38-edc0-4218-aa23-99dcf005b0c8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_admissible_word_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_admissible_word_length_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_leibC
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_spl_len
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_congr_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_Adm_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F}
    (hla : LSS a S) (hlb : LSS b S) {n : ℕ} {Ca Cb : ℝ} {ea eb γ : ℕ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : UB a S n Ca ea γ) (hb : UB b S n Cb eb γ) :
    UB (fun g => a g (b g)) S n (2 ^ n * (Ca * Cb)) (ea + eb) γ := by
  intro w hw g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := hla g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hlb g hg
  have hgG := hSG hg
  have h0 : 0 ≤ gN g := (gN_pos hgG).le
  have hra : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' a g = Dw w' a' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₁ haV g hgG hg₁
  have hrb : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' b g = Dw w' b' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₂ hbV g hgG hg₂
  have happ : Dw w (fun x => a x (b x)) g = Dw w (fun x => a' x (b' x)) g :=
    Dw_congr_loc (admissible_word_mem_lie hw) (hV₁.inter hV₂)
      (fun g' hg' hV => by rw [haV g' hg' hV.1, hbV g' hg' hV.2]) g hgG ⟨hg₁, hg₂⟩
  have key := leibC g (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) w a' b' ha' hb' (by
    intro w₁ w₂ hs
    have hw₁ := Adm_sub hs.1 hw
    have hw₂ := Adm_sub hs.2.1 hw
    rw [← hra w₁ hw₁, ← hrb w₂ hw₂]
    have hexp : ea + γ * w₁.length + (eb + γ * w₂.length) = ea + eb + γ * w.length := by
      rw [← spl_len hs]; ring
    calc ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖
        ≤ (Ca * gN g ^ (ea + γ * w₁.length)) * (Cb * gN g ^ (eb + γ * w₂.length)) :=
          mul_le_mul (ha w₁ hw₁ g hg) (hb w₂ hw₂ g hg) (norm_nonneg _)
            (mul_nonneg hCa (pow_nonneg h0 _))
      _ = Ca * Cb * gN g ^ (ea + γ * w₁.length + (eb + γ * w₂.length)) := by rw [pow_add]; ring
      _ = Ca * Cb * gN g ^ (ea + eb + γ * w.length) := by rw [hexp])
  rw [happ]
  refine key.trans ?_
  have hM : 0 ≤ Ca * Cb * gN g ^ (ea + eb + γ * w.length) :=
    mul_nonneg (mul_nonneg hCa hCb) (pow_nonneg h0 _)
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hw)
  calc (2 : ℝ) ^ w.length * (Ca * Cb * gN g ^ (ea + eb + γ * w.length))
      ≤ 2 ^ n * (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (Ca * Cb) * gN g ^ (ea + eb + γ * w.length) := by ring
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
