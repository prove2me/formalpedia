-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:53:58.853665+00:00
-- url     : https://prove2.me/submissions/056334b7-0aab-4ad0-bbff-6fa48a0cd53d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section RepLemmas
private theorem exists_word_expansion_length_le_add {d e : ℕ} {b : AA k r E} (Lb : List (ℂ × List (Ix k r)))
    (hLb : ∀ q ∈ Lb, q.2.length ≤ e) (hb : ∀ Φ w, b Φ w = (Lb.map fun q => q.1 • Φ (w ++ q.2)).sum) :
    ∀ La : List (ℂ × List (Ix k r)), (∀ p ∈ La, p.2.length ≤ d) →
      ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d + e) ∧
        ∀ Φ w, (La.map fun p => p.1 • (b Φ) (w ++ p.2)).sum = (L.map fun p => p.1 • Φ (w ++ p.2)).sum := by
  intro La
  induction La with
  | nil => intro _; exact ⟨[], by simp, fun _ _ => by simp⟩
  | cons p La ih =>
    intro hLa
    obtain ⟨L, hL, hL'⟩ := ih (fun q hq => hLa q (by simp [hq]))
    refine ⟨(Lb.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ L, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | hq
      · have h1 := hLa p (by simp)
        have h2 := hLb q' hq'
        simp only [List.length_append]
        omega
      · exact hL q hq
    · intro Φ w
      rw [List.map_cons, List.sum_cons, hL' Φ w, List.map_append, List.sum_append, hb, List.smul_sum]
      congr 1
      simp only [List.map_map, Function.comp_def, mul_smul, List.append_assoc]
end RepLemmas
section Words
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Words
section Values
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Values
end Formalism.FourierDecayAlt.P.JFxE
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {d e : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep e b) : Rep (d + e) (a * b) := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  obtain ⟨L, hL, hL'⟩ := exists_word_expansion_length_le_add Lb hLb hb' La hLa
  refine ⟨L, hL, fun Φ w => ?_⟩
  show a (b Φ) w = _
  rw [ha', hL']
end Formalism.FourierDecayAlt.P.JFxE
