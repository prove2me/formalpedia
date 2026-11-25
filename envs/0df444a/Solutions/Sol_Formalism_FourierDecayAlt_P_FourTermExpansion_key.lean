-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:44:03.750728+00:00
-- url     : https://prove2.me/submissions/8e7573a9-9d34-4dc2-83ef-d820663d90d9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_four
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc ((m + 1 : ℕ) : ℕ∞) Φ g) :
    PP a b u σ Φ g - PP a b u (σ * Equiv.swap i.castSucc i.succ) Φ g
      + PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g
      - PP a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) Φ g = 0 := by
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hsw : ∀ j : Fin (m + 1), (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → Equiv.swap i.castSucc i.succ j = j :=
    fun j h1 h2 => Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h, Fin.coe_castSucc]))
      (fun h => h2 (by rw [h, Fin.val_succ]))
  have hc : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
  have hs : (⟨(i : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
  refine four (f₁ := fun j => (u - ((j : ℕ) : ℂ), a (σ j), b j))
    (f₂ := fun j => (u - ((j : ℕ) : ℂ), a ((σ * Equiv.swap i.castSucc i.succ) j), b j))
    (f₃ := fun j => (u - ((j : ℕ) : ℂ), a (σ j), (b ∘ Equiv.swap i.castSucc i.succ) j))
    (f₄ := fun j => (u - ((j : ℕ) : ℂ), a ((σ * Equiv.swap i.castSucc i.succ) j), (b ∘ Equiv.swap i.castSucc i.succ) j))
    (i : ℕ) hi ?_ ?_ ?_ ?_ Φ g hg hloc
  · intro j h1 h2; simp only [Equiv.Perm.mul_apply, hsw j h1 h2]
  · intro j h1 h2; simp only [Function.comp_apply, hsw j h1 h2]
  · intro j h1 h2; simp only [Equiv.Perm.mul_apply, Function.comp_apply, hsw j h1 h2]
  · intro Ψ x hx hΨ
    simp only [hc, hs, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Fin.coe_castSucc, Fin.val_succ]
    exact two hΨ hx _ _ (by push_cast; ring) _ _ _ _
end Formalism.FourierDecayAlt.P.FourTermExpansion
