-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_excW_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:51.344867+00:00
-- url     : https://prove2.me/submissions/90cd595d-e631-4325-8fd1-6da0c8c02b0e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
