-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:15.185124+00:00
-- url     : https://prove2.me/submissions/400f6273-a302-4260-8f0f-b2513439c5aa

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_spread
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_REAL_drop_ofFn_congr
import Theorems.Thm_Formalism_REAL_take_ofFn_congr


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
theorem _root_.solution {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ)
    (hi : i + 1 < t)
    (h₂ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₂ j = f₁ j)
    (h₃ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₃ j = f₁ j)
    (h₄ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₄ j = f₁ j)
    (hmid : ∀ (Ψ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc 2 Ψ x →
      (let P := fun (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) =>
        Top (LT (Msg k r)) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
          (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2 Ψ) x
       P f₁ - P f₂ + P f₃ - P f₄ = 0))
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) :
    fold (Msg k r) (List.ofFn f₁) Φ g - fold (Msg k r) (List.ofFn f₂) Φ g +
      fold (Msg k r) (List.ofFn f₃) Φ g - fold (Msg k r) (List.ofFn f₄) Φ g = 0 := by
  rw [split _ f₁ i hi, split _ f₂ i hi, split _ f₃ i hi, split _ f₄ i hi,
    Formalism.REAL.take_ofFn_congr f₂ f₁ i (fun j hj => h₂ j (by omega) (by omega)),
    Formalism.REAL.take_ofFn_congr f₃ f₁ i (fun j hj => h₃ j (by omega) (by omega)),
    Formalism.REAL.take_ofFn_congr f₄ f₁ i (fun j hj => h₄ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₂ f₁ (i + 2) (fun j hj => h₂ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₃ f₁ (i + 2) (fun j hj => h₃ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₄ f₁ (i + 2) (fun j hj => h₄ j (by omega) (by omega))]
  set L := (List.ofFn f₁).take i with hL
  set Ψ := fold (Msg k r) ((List.ofFn f₁).drop (i + 2)) Φ with hΨ
  have hLlen : L.length = i := by simp [hL]; omega
  have hdlen : ((List.ofFn f₁).drop (i + 2)).length + (i + 2) = t := by simp; omega

  set P : (Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → Mat k r → E := fun f =>
    Top (LT (Msg k r)) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
      (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2 Ψ) with hP
  show fold (Msg k r) L (P f₁) g - fold (Msg k r) L (P f₂) g + fold (Msg k r) L (P f₃) g -
    fold (Msg k r) L (P f₄) g = 0
  obtain ⟨U, hU, hgU, hUl⟩ := loc_spread hloc
  have hΨloc : ∀ x ∈ U, Loc ((i + 2 : ℕ) : ℕ∞) Ψ x := by
    intro x hx
    apply fold_loc (Msg k r) _ (i + 2) Φ x
    rw [add_comm, hdlen]; exact hUl x hx
  have hPloc : ∀ f, Loc ((L.length : ℕ) : ℕ∞) (P f) g := by
    intro f
    rw [hLlen]
    have h := hΨloc g hgU
    have : Loc ((i + 1 : ℕ) : ℕ∞ ) (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1
        (f ⟨i + 1, hi⟩).2.2 Ψ) g := top_loc _ (by exact_mod_cast h) _ _ _
    exact top_loc _ (by exact_mod_cast this) _ _ _
  set Q12 : Mat k r → E := fun w => P f₁ w + (-1 : ℂ) • P f₂ w with hQ12
  set Q123 : Mat k r → E := fun w => Q12 w + (1 : ℂ) • P f₃ w with hQ123
  set F : Mat k r → E := fun w => Q123 w + (-1 : ℂ) • P f₄ w with hF
  have lQ12 : Loc ((L.length : ℕ) : ℕ∞) Q12 g := loc_add (hPloc f₁) (hPloc f₂) (-1 : ℂ)
  have lQ123 : Loc ((L.length : ℕ) : ℕ∞) Q123 g := loc_add lQ12 (hPloc f₃) 1
  have hvan : ∀ x ∈ U, x ∈ GV k r → F x = (fun _ => (0 : E)) x := by
    intro x hx hxG
    have := hmid Ψ x hxG (loc_mono (by norm_num) (hΨloc x hx))
    simp only at this
    simp only [hF, hQ123, hQ12, neg_one_smul, one_smul]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    exact this
  have e1 : fold (Msg k r) L F g = fold (Msg k r) L Q123 g + (-1 : ℂ) • fold (Msg k r) L (P f₄) g :=
    fold_lin (Msg k r) L Q123 (P f₄) g hg lQ123 (hPloc f₄) (-1)
  have e2 : fold (Msg k r) L Q123 g = fold (Msg k r) L Q12 g + (1 : ℂ) • fold (Msg k r) L (P f₃) g :=
    fold_lin (Msg k r) L Q12 (P f₃) g hg lQ12 (hPloc f₃) 1
  have e3 : fold (Msg k r) L Q12 g = fold (Msg k r) L (P f₁) g + (-1 : ℂ) • fold (Msg k r) L (P f₂) g :=
    fold_lin (Msg k r) L (P f₁) (P f₂) g hg (hPloc f₁) (hPloc f₂) (-1)
  have hzero : fold (Msg k r) L F g = 0 := by
    rw [fold_congr (Msg k r) L hU hvan g hgU hg, fold_zero (Msg k r) L g hg]
  rw [e1, e2, e3] at hzero
  simp only [neg_one_smul, one_smul] at hzero
  rw [← hzero]; abel
end Formalism.FourierDecayAlt.P.FourTermExpansion
