-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.column_parametrization_top_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:29.363734+00:00
-- url     : https://prove2.me/submissions/404a75f7-e926-4099-a9ad-672d15373bd6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ColumnParametrizationOffDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
private theorem g4w9_dec (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta) :
    ∀ d i, i + d < 2 * K → U (i + d) + (d : ℤ) ≤ U i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := L.chain (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := by omega
    rw [e]
    push_cast
    linarith [h2.1, h2.2]
private theorem g4w9_dec' (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (i j : ℕ) (hij : i ≤ j) (hj : j < 2 * K) : U j + (j : ℤ) ≤ U i + (i : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h := g4w9_dec K m s U v b e S eta L d i (by omega)
  push_cast
  linarith
private theorem g4w9_anti (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (hκ : κ + 1 = 2 * K) : Antitone (colW K U (k := κ + 1)) := by
  intro i j hij
  have hj : (j : ℕ) < 2 * K := by have := j.isLt; omega
  have h := g4w9_dec' K m s U v b e S eta L i j (Fin.le_iff_val_le_val.mp hij) hj
  simp only [colW]
  linarith
end Formalism.HermitianLattices.ExplicitEstimates
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : ColumnParameterMaximalCondition := by
  intro K m s κ U v b e S eta A bt L hT hκ
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  refine ⟨g4w9_anti K m s κ U v b e S eta L hκ, ?_, ?_, ?_⟩
  · rw [hcw]
    simp only [Fin.val_zero, Nat.cast_zero]
    linarith [hT.1]
  · rw [hcw, Fin.val_last]
    have e0 : 2 * K - 1 = κ := by omega
    have h2 := hT.2
    rw [e0] at h2
    linarith
  · intro i hi0 hil
    have hi := i.isLt
    have h0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
    have hl : (i : ℕ) ≠ κ := fun h => hil (Fin.ext (by simpa using h))
    have hA := g4w9_dec' K m s U v b e S eta L 1 i (by omega) (by omega)
    have hB := g4w9_dec' K m s U v b e S eta L i (2 * K - 2) (by omega) (by omega)
    have hc1 := L.cloud_u 1 le_rfl (by omega)
    have hc2 := L.cloud_u (2 * K - 2) (by omega) (by omega)
    have e2 : (((2 * K - 2 : ℕ)) : ℤ) = 2 * (K : ℤ) - 2 := by omega
    rw [hcw]
    push_cast at hA
    constructor <;> linarith [hc1.2, hc2.1]
end Formalism.HermitianLattices.ExplicitEstimates
