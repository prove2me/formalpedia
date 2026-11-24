-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.corollary_s_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:11.785996+00:00
-- url     : https://prove2.me/submissions/7f3e64b8-3ac5-463a-bb84-ab5cfdd9eb4f

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_admissible_word_of_extension
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_len
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (C₂ : ℝ) (hC : 0 ≤ C₂)
    (hL : LemmaS p nn F Y Λ K N C₂) :
    ∀ γ : C.LPt, ∀ j, D.IsLocPt γ j → j ≤ P.r + 1 → ∀ w, AdmW P p.l0 Y w → w.length + j * K ≤ N →
      ∃ w', IsExt P p.l0 Y N (j * K) w w' ∧ Ew p nn F j w γ ≤ (C₂ * Λ ^ 2) ^ j * Ew p nn F 0 w' [] := by
  have hCL : 0 ≤ C₂ * Λ ^ 2 := by positivity
  intro γ
  induction γ using List.reverseRecOn with
  | nil =>
    intro j hj _ w hw hl
    have hj0 : j = 0 := by simpa [D.IsLocPt, D.ptSize] using hj.2.symm
    subst hj0
    exact ⟨w, isExt_self hw (by omega), by simp⟩
  | append_singleton h x ih =>
    intro j hj hjr w hw hl
    obtain ⟨s, t⟩ := x
    obtain ⟨hblk, hsz⟩ := hj
    have hsz' : D.ptSize h + s = j := by simpa [D.ptSize] using hsz
    have hst := hblk (s, t) (by simp)
    have hh : D.IsLocPt h (D.ptSize h) := ⟨fun bl hbl => hblk bl (by simp [hbl]), rfl⟩
    set i := D.ptSize h with hi
    have hlS : w.length + s * K ≤ N := by
      have : s * K ≤ j * K := Nat.mul_le_mul_right K (by omega)
      omega
    obtain ⟨w₁, hw₁, hE₁⟩ := hL (i + 1) s (by omega) hst.1 (by omega) h (by simpa using hh) w hw hlS t hst.2
    rw [show i + 1 + s - 1 = j by omega, show i + 1 - 1 = i by omega] at hE₁
    have hl₁ : w₁.length + i * K ≤ N := by
      have h1 := isExt_len hw₁
      have : j * K = i * K + s * K := by rw [← hsz', Nat.add_mul]
      omega
    obtain ⟨w₂, hw₂, hE₂⟩ := ih i hh (by omega) w₁ (admissible_word_of_extension hw hw₁) hl₁
    refine ⟨w₂, ?_, hE₁.trans ?_⟩
    · refine isExt_mono (isExt_trans hw₁ hw₂) (le_of_eq ?_)
      rw [← hsz', Nat.add_mul, add_comm]
    · calc (C₂ * Λ ^ 2) ^ s * Ew p nn F i w₁ h
          ≤ (C₂ * Λ ^ 2) ^ s * ((C₂ * Λ ^ 2) ^ i * Ew p nn F 0 w₂ []) :=
            mul_le_mul_of_nonneg_left hE₂ (pow_nonneg hCL _)
        _ = (C₂ * Λ ^ 2) ^ j * Ew p nn F 0 w₂ [] := by rw [← hsz', pow_add]; ring
end Formalism.FourierDecayAlt.P.TBBx1
