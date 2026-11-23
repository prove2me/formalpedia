-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.four_formal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.590834+00:00
-- url     : https://prove2.me/submissions/d363ca81-8dce-4878-ac34-e55431d9ff1c

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Theorems.Thm_Formalism_REAL_drop_ofFn_congr
import Theorems.Thm_Formalism_REAL_prod_ofFn_split_pair
import Theorems.Thm_Formalism_REAL_sandwich_alternating_sum
import Theorems.Thm_Formalism_REAL_take_ofFn_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod =
      ((List.ofFn f₁).take i).prod * (f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
        + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩) *
        ((List.ofFn f₁).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi, prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)), sandwich_alternating_sum]
end Formalism.FourierDecayAlt.P.JFxE
