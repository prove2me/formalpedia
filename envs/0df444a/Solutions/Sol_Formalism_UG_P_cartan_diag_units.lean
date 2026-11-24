-- Prove2me | solution 1 for Formalism.UG.P.cartan_diag_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:08.517801+00:00
-- url     : https://prove2.me/submissions/2a056d1c-1d5d-4e76-8506-645ffd4d5744

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hU : ∀ x : L, x ≠ 0 → ∃ k : ℤ, val x = val ϖ ^ k) {m : ℕ} (d : Fin m → L)
    (hd : ∀ i, d i ≠ 0) :
    ∃ a : Fin m → ℤ, ∃ U ∈ GLint (Fin m) O,
      Matrix.diagonal d = (U : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) := by
  choose a ha using fun i => hU (d i) (hd i)
  have hvϖ : val ϖ ≠ 0 := (Valuation.ne_zero_iff val).mpr hϖ0
  refine ⟨a, ?_⟩
  have hAB : (Matrix.diagonal fun i => d i * ϖ ^ (-a i)) * (Matrix.diagonal fun i => (d i)⁻¹ * ϖ ^ a i) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hd i
    have h2 := zpow_ne_zero (a i) hϖ0
    rw [_root_.zpow_neg]
    field_simp
  have hA : ∀ i j, (Matrix.diagonal fun i => d i * ϖ ^ (-a i)) i j ∈ O := by
    intro i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (hO _).mpr (le_of_eq (by
        rw [map_mul, map_zpow₀, ha i, ← zpow_add₀ hvϖ, add_neg_cancel, zpow_zero]))
    · exact O.zero_mem
  have hB : ∀ i j, (Matrix.diagonal fun i => (d i)⁻¹ * ϖ ^ a i) i j ∈ O := by
    intro i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (hO _).mpr (le_of_eq (by
        rw [map_mul, map_inv₀, map_zpow₀, ha i, inv_mul_cancel₀ (zpow_ne_zero _ hvϖ)]))
    · exact O.zero_mem
  obtain ⟨U, hUm, hUA⟩ := cartan_exists_glint O _ _ hAB hA hB
  refine ⟨U, hUm, ?_⟩
  rw [hUA, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, mul_one]
end Formalism.UG.P
