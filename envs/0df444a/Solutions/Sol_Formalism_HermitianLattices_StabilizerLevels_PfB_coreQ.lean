-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.coreQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:31.137932+00:00
-- url     : https://prove2.me/submissions/f41089b6-6b4b-4054-b947-4facbc5f3ef9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_sqf_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFixed
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gensModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (τ₁ τ₂ τ₃ : Gal(L/ℚ)) (h1 : galMap h.1 a b τ₁ = ((1, -1, 1) : GalL (e + 2)))
    (h2 : galMap h.1 a b τ₂ = ((1, 1, -1) : GalL (e + 2)))
    (h3 : galMap h.1 a b τ₃ = ((u5 (e + 2), 1, 1) : GalL (e + 2)))
    (X y : L) (hX : X ∈ hostE ζ a b) (hy : y ∈ hostE ζ a b) (m m' : ℤ) (hm : Squarefree m)
    (hm' : Squarefree m') (hXm : X ^ 2 = (m : L)) (hym : y ^ 2 = (m' : L))
    (r1 : τ₁ X * y = X * τ₁ y) (r2 : τ₂ X * y = X * τ₂ y) (r3 : τ₃ X * y = X * τ₃ y) : m = m' := by
  obtain ⟨hGal, -, hmul, hbij⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (m' : L) = 0 := by rw [← hym]; ring
    have : m' = 0 := by exact_mod_cast this
    rw [this] at hm'
    exact not_squarefree_zero hm'
  obtain ⟨τ₀, h0⟩ := hbij.2 ((-1, 1, 1) : GalL (e + 2))
  have hfix0 : ∀ x ∈ hostE ζ a b, τ₀ x = x := fun x hx =>
    ((hostFixed e q d hqd L ζ a b h).2 x).1 hx τ₀ h0
  have hrel : ∀ τ : Gal(L/ℚ), τ X * y = X * τ y → τ (X / y) = X / y := by
    intro τ hτ
    have : τ y ≠ 0 := by simpa using hy0
    rw [map_div₀, div_eq_div_iff this hy0, hτ]
  let φ : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmul
  let S : Subgroup Gal(L/ℚ) := MulAction.stabilizer Gal(L/ℚ) (X / y)
  have hS : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y → τ ∈ S := fun τ hτ => hτ
  have htop : S.map φ = ⊤ := by
    rw [eq_top_iff, ← (gensModel (e + 2) (by omega)).2.2.2.2, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact ⟨τ₀, hS _ (hrel _ (by rw [hfix0 X hX, hfix0 y hy])), h0⟩
    · exact ⟨τ₃, hS _ (hrel _ r3), h3⟩
    · exact ⟨τ₁, hS _ (hrel _ r1), h1⟩
    · exact ⟨τ₂, hS _ (hrel _ r2), h2⟩
  have hall : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y := by
    intro τ
    have : φ τ ∈ S.map φ := by rw [htop]; trivial
    obtain ⟨τ', hτ', he⟩ := this
    have : τ' = τ := hbij.1 he
    rw [← this]; exact hτ'
  have hbot := (IsGalois.mem_bot_iff_fixed (F := ℚ) (E := L) (X / y)).2 hall
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hbot
  apply sqf_eq m m' hm hm' c
  have hXc : X = algebraMap ℚ L c * y := by rw [hc]; field_simp
  have : ((m : ℚ) : L) = ((c ^ 2 * m' : ℚ) : L) := by
    push_cast
    rw [← hXm, ← hym, hXc]
    simp only [eq_ratCast]
    ring
  exact_mod_cast this
end Formalism.HermitianLattices.StabilizerLevels.PfB
