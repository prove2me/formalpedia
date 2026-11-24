-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.fdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:50.586827+00:00
-- url     : https://prove2.me/submissions/252cab58-b577-4b38-8db7-7a78f51ab80b

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dif
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cdx
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_leibA
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_spl_len
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section app
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
private lemma dw_append_singleton' {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (w : List (Bool × Mat k r))
    (x : Bool × Mat k r) (f : Mat k r → E') : Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl
private theorem adm_of_sublist {n : ℕ} {w w' : List (Bool × Mat k r)} (h : admitted n w)
    (hw : w'.Sublist w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hlen, rfl⟩ := h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hw
  unfold wL at h1
  unfold wR at h2
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 h1
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 h2
  exact ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX),
    by have := hu'.length_le; have := hv'.length_le; omega, rfl⟩
end app
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (K : Set F) (hK : ∀ g ∈ S, ψ g ∈ K)
    (Y : Mat k r → ℝ) (hY : ∀ g ∈ S, 1 ≤ Y g) (α β : ℕ) (M : ℝ) (n : ℕ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ S, ‖Dw w ψ g‖ ≤ M * Y g ^ (α * w.length + β)) :
    ∀ m : ℕ, ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] (Φ : F → E₁), ContDiff ℝ ∞ Φ →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ S,
        ‖Dw w (fun g => Φ (ψ g)) g‖ ≤ C * Y g ^ ((α + β) * w.length) := by
  intro m
  induction m with
  | zero =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨B0, hB0⟩ := hB 0
    refine ⟨max B0 0, le_max_right _ _, fun w _ hw g hg => ?_⟩
    have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst hw0
    simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
    have h0 := hB0 (ψ g) (hK g hg)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left _ _)
  | succ m ih =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨C', hC'0, hC'⟩ := ih (F →L[ℝ] E₁) (fderiv ℝ Φ) (hΦ.fderiv_right (m := ∞) (by simp))
      (fun j => by
        obtain ⟨B, hB'⟩ := hB (j + 1)
        exact ⟨B, fun y hy => by rw [norm_iteratedFDeriv_fderiv]; exact hB' y hy⟩)
    obtain ⟨B0, hB0⟩ := hB 0
    have hM' : 0 ≤ max M 0 := le_max_right _ _
    refine ⟨max B0 0 + 2 ^ m * (C' * max M 0),
      add_nonneg (le_max_right _ _) (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')),
      fun w hwA hw g hg => ?_⟩
    have hY1 := hY g hg
    have hY0 : 0 ≤ Y g := by linarith
    have hrest : 0 ≤ 2 ^ m * (C' * max M 0) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
      have h0 := hB0 (ψ g) (hK g hg)
      rw [norm_iteratedFDeriv_zero] at h0
      linarith [le_max_left B0 0]
    · rw [List.concat_eq_append] at hwA hw ⊢
      rw [dw_append_singleton', dx_comp x (dif hψ) (dif hΦ)]
      have hlen : w'.length ≤ m := by
        rw [List.length_append, List.length_singleton] at hw
        omega
      have key := leibA g (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) w'
        (fun g => fderiv ℝ Φ (ψ g)) (Dx x ψ) ((hΦ.fderiv_right (m := ∞) (by simp)).comp hψ) (cdx x hψ)
        (fun w₁ w₂ hs => by
          have hl := spl_len hs
          have h1 : ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ ≤ C' * Y g ^ ((α + β) * w₁.length) :=
            hC' w₁ (adm_of_sublist hwA (hs.1.trans (List.sublist_append_left _ _))) (by omega) g hg
          have h2 : ‖Dw w₂ (Dx x ψ) g‖ ≤ max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β) := by
            rw [← dw_append_singleton']
            exact (H (w₂ ++ [x]) (adm_of_sublist hwA (hs.2.1.append_right [x])) (by simp) g hg).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hY0 _))
          have hexp : (α + β) * w₁.length + (α * (w₂ ++ [x]).length + β) ≤
              (α + β) * (w'.length + 1) := by
            rw [List.length_append, List.length_singleton]
            nlinarith
          calc ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ * ‖Dw w₂ (Dx x ψ) g‖
              ≤ (C' * Y g ^ ((α + β) * w₁.length)) * (max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC'0 (pow_nonneg hY0 _))
            _ = C' * max M 0 * Y g ^ ((α + β) * w₁.length + (α * (w₂ ++ [x]).length + β)) := by
                rw [pow_add]
                ring
            _ ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (mul_nonneg hC'0 hM'))
      have hP : 0 ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
        mul_nonneg (mul_nonneg hC'0 hM') (pow_nonneg hY0 _)
      calc _ ≤ 2 ^ w'.length * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) := key
        _ ≤ 2 ^ m * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hP
        _ ≤ (max B0 0 + 2 ^ m * (C' * max M 0)) * Y g ^ ((α + β) * (w' ++ [x]).length) := by
            rw [List.length_append, List.length_singleton]
            have : 0 ≤ max B0 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
              mul_nonneg (le_max_right _ _) (pow_nonneg hY0 _)
            nlinarith
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
