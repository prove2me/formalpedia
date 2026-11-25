-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_Fchi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:00.338412+00:00
-- url     : https://prove2.me/submissions/aaf74d3d-5291-4958-ab15-059ad33959bc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rect_double
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rectInt_congr
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rectInt_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exKer_continuousAt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_bdry_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_differentiable
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_re_lt_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rect_logDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
private theorem neg_div_mul_eq_neg_add_div_mul_add_div (a b K u : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) :
    -(b / a) * K = -((1 * a + u * b) / (u * a)) * K + K / u := by
  field_simp
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by
  have hfd : Differentiable ℂ (exLF χ) := exLF_differentiable χ
  have hx : σ₁ ≤ σ₀ := by linarith
  have hyy : -T' ≤ T' := by linarith
  have hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T' := by
    intro ρ
    rw [hZ ρ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have := exLF_re_lt_one χ h0
      exact ⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩
    · rintro ⟨h0, h1, -, h3, h4⟩
      exact ⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩
  have hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 →
      σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T' := by
    intro w h1 h2 h3 h4 h0
    obtain ⟨h5, h6⟩ := hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0
    have := exLF_re_lt_one χ h0
    exact ⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩
  have hmain := ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀
    (by linarith) hT' Z hZ' hedge'
  by_cases hχ : χ = 1
  · subst hχ
    have hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0 := by
      intro w hw
      obtain ⟨h0, h1⟩ := ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw
      refine ⟨h0, h1, fun hfw => ?_⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hedge' w a1 a2 a3 a4 hfw
      rcases a5 with h | h | h | h <;> linarith
    have hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w /
        exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w :=
        (hfd.analyticAt w).deriv.continuousAt
      exact (((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt
    have hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, -⟩ := hbd w hw
      have hs : ContinuousAt (fun s : ℂ => s - 1) w := continuousAt_id.sub continuousAt_const
      exact ((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt
    have hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w =
        -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w +
          exKer y w / (w - 1) := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hfw : exLF (1 : DirichletCharacter ℂ M) w =
          (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := exLF_one_char_apply h1
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0 := by
        intro h
        apply h2
        rw [hfw, h, mul_zero]
      have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w :=
        DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)
      have hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w]
          fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s :=
        (eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs
      have hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w =
          1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w +
            (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w := by
        rw [hev.deriv_eq]
        exact (((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv
      have e1 : Fchi (1 : DirichletCharacter ℂ M) y w =
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w := by
        simp only [Fchi, negLD, exKer, mul_div_assoc]
      rw [e1, hder, hfw]
      exact neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1
    rw [ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain,
      ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]
    simp only [explicitFormulaConstant, exOrd]
    ring
  · have hfL : exLF χ = DirichletCharacter.LFunction χ := exLF_of_ne hχ
    have hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w := by
      funext w
      simp only [Fchi, negLD, exKer, hfL, mul_div_assoc]
    rw [hF, hmain, if_neg hχ]
    simp only [explicitFormulaConstant, exOrd]
    ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
