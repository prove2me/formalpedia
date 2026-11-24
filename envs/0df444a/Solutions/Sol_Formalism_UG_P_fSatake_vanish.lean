-- Prove2me | solution 1 for Formalism.UG.P.fSatake_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:17.608844+00:00
-- url     : https://prove2.me/submissions/2fdef71e-0d96-4509-8052-4a2d81f72366

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Theorems.Thm_Formalism_UG_P_fSatake_borel_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG
noncomputable section
namespace Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
private lemma isBorelU_mul {b c : GU σ n} (hb : IsBorelU b) (hc : IsBorelU c) :
    IsBorelU (b * c) := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  have hC : Matrix.BlockTriangular ⟪c⟫ id := fun i j h => hc i j h
  intro i j hij
  show (⟪b⟫ * ⟪c⟫) i j = 0
  exact (hB.mul hC) hij
private lemma isBorelU_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  letI : Invertible ⟪b⟫ := Units.invertible _
  have hinv : ⟪b⁻¹⟫ = (⟪b⟫)⁻¹ := by simp [Matrix.coe_units_inv]
  intro i j hij
  change ⟪b⁻¹⟫ i j = 0
  rw [hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB hij
end Formalism.UG.P
end
end

set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (x : GU σ n)
    (hx : ¬ ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ x = b * k) : φ x = 0 := by
  classical
  obtain ⟨φ0, -, -, huniq⟩ := hSph L ϖ σ q n m hU hm hm' α hα
  have hP : ∀ b g k : GU σ n, IsBorelU b → k ∈ KU σ n →
      ((∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k') ↔
        (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k')) := by
    intro b g k hb hk
    constructor
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b⁻¹ * b', k' * k⁻¹, isBorelU_mul (isBorelU_inv hb) hb',
        (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk), ?_⟩
      calc g = b⁻¹ * (b * g * k) * k⁻¹ := by group
        _ = b⁻¹ * b' * (k' * k⁻¹) := by rw [he]; group
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b * b', k' * k, isBorelU_mul hb hb', (KU σ n).mul_mem hk' hk, ?_⟩
      rw [he]
      group
  let ψ : GU σ n → ℂ := fun g =>
    if (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k') then φ g else 0
  have hψ : IsSphericalU q α ψ := by
    intro b g k hb hk
    by_cases hg : ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k'
    · have h1 := (hP b g k hb hk).2 hg
      simp only [ψ, if_pos h1, if_pos hg]
      exact hφ b g k hb hk
    · have h1 : ¬ ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k' :=
        fun h => hg ((hP b g k hb hk).1 h)
      simp only [ψ, if_neg h1, if_neg hg, mul_zero]
  have hψ1 : ψ 1 = φ 1 := by
    simp only [ψ]
    exact if_pos ⟨1, 1, fSatake_borel_one, (KU σ n).one_mem, by simp⟩
  have hψx : ψ x = 0 := by
    simp only [ψ]
    exact if_neg hx
  have e1 : ψ x = ψ 1 * φ0 x := congrFun (huniq ψ hψ) x
  have e2 : φ x = φ 1 * φ0 x := congrFun (huniq φ hφ) x
  rw [e2, ← hψ1, ← e1, hψx]
end Formalism.UG.P
