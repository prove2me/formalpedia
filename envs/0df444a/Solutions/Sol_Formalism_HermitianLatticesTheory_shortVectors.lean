-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.shortVectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:51.444147+00:00
-- url     : https://prove2.me/submissions/36ea1db0-54b4-49f0-8ea2-4382557aa147

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_SuccessiveMinima_MinkowskiIIUpper
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors
import Theorems.Thm_Formalism_FN_existsSuccessiveMinimaVectors
import Theorems.Thm_Formalism_FN_minkowskiIIUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
namespace Formalism.HermitianLatticesTheory
private lemma shortVectors_norm_le {N : ℕ} {t : ℝ} (ht : 0 < t) {u : EuclideanSpace ℝ (Fin N)}
    (hu : u ∈ t • closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) : ‖u‖ ≤ t := by
  obtain ⟨v, hv, rfl⟩ := hu
  rw [mem_closedBall_zero_iff] at hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_le_of_le_one_right ht.le hv
private lemma shortVectors_prod_ge {n : ℕ} {c : ℝ} (hc : 0 < c) (lam : Fin n → ℝ)
    (hlow : ∀ i, c ≤ lam i) (j : Fin n) : lam j * c ^ (n - 1) ≤ ∏ i, lam i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ j)]
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have h1 : c ^ (n - 1) ≤ ∏ i ∈ Finset.univ.erase j, lam i := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => hc.le) (fun i _ => hlow i)
  have hj : 0 ≤ lam j := le_trans hc.le (hlow j)
  exact mul_le_mul_of_nonneg_left h1 hj
private lemma shortVectors_vol_pos (N : ℕ) :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
  show 0 < (volume (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne' measure_closedBall_lt_top.ne
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : ShortVectors := by
  intro N c C hc
  refine ⟨2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C /
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)), ?_⟩
  intro Λ _ _ hmin hcov
  have hK : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := isCompact_closedBall 0 1
  have hconv : Convex ℝ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := convex_closedBall 0 1
  have hsym : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1,
      -x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    rwa [norm_neg]
  have hint : (0 : EuclideanSpace ℝ (Fin N)) ∈
      interior (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact mem_ball_self one_pos
  obtain ⟨v, hli, hvL, hvK, hpos, -, -⟩ := Formalism.FN.existsSuccessiveMinimaVectors Λ _ hK hconv hsym hint
  have hM := Formalism.FN.minkowskiIIUpper (volume : Measure (EuclideanSpace ℝ (Fin N))) Λ _
    hK hconv hsym hint
  have hV := shortVectors_vol_pos N
  have hlow : ∀ i : Fin (finrank ℝ (EuclideanSpace ℝ (Fin N))), c ≤ Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
      ((i : ℕ) + 1) := by
    intro i
    exact le_trans (hmin _ (hvL i) (hli.ne_zero i)) (shortVectors_norm_le (hpos i) (hvK i))
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  refine ⟨fun i => v (Fin.cast hN.symm i), fun i => hvL _,
    hli.comp _ (Fin.cast_injective _), fun i => ?_⟩
  refine le_trans (shortVectors_norm_le (hpos _) (hvK _)) ?_
  have hcp : 0 < c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1) := pow_pos hc _
  rw [le_div_iff₀ (mul_pos hV hcp)]
  have h1 := shortVectors_prod_ge hc
    (fun i => Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) ((i : ℕ) + 1))
    hlow (Fin.cast hN.symm i)
  have h2 : (2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * ZLattice.covolume Λ ≤
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C :=
    mul_le_mul_of_nonneg_left hcov (by positivity)
  have h3 := mul_le_mul_of_nonneg_left h1 hV.le
  calc _ = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        (Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
          ((Fin.cast hN.symm i : ℕ) + 1) * c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)) := by
        ring
    _ ≤ _ := h3
    _ ≤ _ := hM
    _ ≤ _ := h2
end Formalism.HermitianLatticesTheory
