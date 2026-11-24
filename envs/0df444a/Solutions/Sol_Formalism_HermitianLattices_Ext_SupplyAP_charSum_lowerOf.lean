-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.charSum_lowerOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:12.824926+00:00
-- url     : https://prove2.me/submissions/9bbb372a-eb26-4af6-bb69-b075e779744d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excTerm_ofReal
import Theorems.Thm_Formalism_ZeroFreeDirichlet_card_dirichletCharacter_eq_totient
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_progression_orthogonality
import Theorems.Thm_Formalism_ZeroFreeDirichlet_principal_character_orthogonality_term


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x K : ℝ) (hx : 0 ≤ x)
    (B : DirichletCharacter ℂ q → Finset ℝ) (hB : ∀ χ, ∀ β ∈ B χ, 0 ≤ β)
    (hE : ∀ χ, ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ K) :
    x - ∑ χ : DirichletCharacter ℂ q, ∑ β ∈ B χ, x ^ β / β - (q.totient : ℝ) * K ≤
      (q.totient : ℝ) * psiAP q a x := by
  set S : DirichletCharacter ℂ q → ℝ := fun χ => ∑ β ∈ B χ, x ^ β / β with hS
  set E : DirichletCharacter ℂ q → ℂ := fun χ => psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ) with hEdef
  have hSnn : ∀ χ, 0 ≤ S χ := fun χ =>
    Finset.sum_nonneg (fun β hβ => div_nonneg (Real.rpow_nonneg hx β) (hB χ β hβ))
  have hT : ∀ χ, ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ) = ((S χ : ℝ) : ℂ) := by
    intro χ
    simp only [hS, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun β _ => excTerm_ofReal x β hx)
  have hsplit : ∀ χ, psiChi χ x = (if χ = 1 then (x : ℂ) else 0) + (E χ - ((S χ : ℝ) : ℂ)) := by
    intro χ
    simp only [hEdef, hT]
    ring
  set W : ℂ := ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (E χ - ((S χ : ℝ) : ℂ)) with hW
  have hid : (((q.totient : ℝ) * psiAP q a x : ℝ) : ℂ) = (x : ℂ) + W := by
    have h0 := chebyshev_progression_orthogonality q a ha x
    simp only [hsplit, mul_add, Finset.sum_add_distrib, principal_character_orthogonality_term q a ha x] at h0
    push_cast
    rw [h0]
  have hre : (q.totient : ℝ) * psiAP q a x = x + W.re := by
    have := congrArg Complex.re hid
    simpa using this
  have hWn : ‖W‖ ≤ (q.totient : ℝ) * K + ∑ χ : DirichletCharacter ℂ q, S χ := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ‖χ ((a : ZMod q)⁻¹) * (E χ - ((S χ : ℝ) : ℂ))‖ ≤ K + S χ := by
      intro χ _
      rw [norm_mul]
      have h3 := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
      have h4 : ‖E χ - ((S χ : ℝ) : ℂ)‖ ≤ K + S χ := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSnn χ)]
        have := hE χ
        linarith
      calc ‖χ ((a : ZMod q)⁻¹)‖ * ‖E χ - ((S χ : ℝ) : ℂ)‖ ≤ 1 * ‖E χ - ((S χ : ℝ) : ℂ)‖ := by
            gcongr
        _ ≤ K + S χ := by rw [one_mul]; exact h4
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_dirichletCharacter_eq_totient]
  have hreW : -‖W‖ ≤ W.re := by
    have := Complex.abs_re_le_norm W
    linarith [neg_abs_le W.re]
  show x - ∑ χ : DirichletCharacter ℂ q, S χ - (q.totient : ℝ) * K ≤ _
  linarith
end Formalism.HermitianLattices.Ext.SupplyAP
