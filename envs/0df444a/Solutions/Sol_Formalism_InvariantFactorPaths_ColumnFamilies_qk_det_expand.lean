-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.654845+00:00
-- url     : https://prove2.me/submissions/73ace01d-ccc5-4afb-9db3-cc1cb81a4359

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (v w : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      ∑ s : Finset (Fin n), x ^ s.card * (Matrix.vandermonde (s.piecewise w v)).det := by
  have hV : ∀ u : Fin n → R, (Matrix.vandermonde u).det =
      Matrix.detRowAlternating (fun (i j : Fin n) => u i ^ (j : ℕ)) := fun u => rfl
  have h0 : (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      Matrix.detRowAlternating ((fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) +
        fun (i j : Fin n) => v i ^ (j : ℕ)) := by
    show Matrix.detRowAlternating _ = _
    congr 1
    funext i j
    simp [add_comm]
  rw [h0, AlternatingMap.map_add_univ]
  refine sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) (fun (i j : Fin n) => v i ^ (j : ℕ)) =
      s.piecewise (fun i => (fun _ => x) i • (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) i)
        (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) := by
    funext i
    by_cases hi : i ∈ s
    · simp only [piecewise_eq_of_mem _ _ _ hi]
    · simp only [piecewise_eq_of_notMem _ _ _ hi]
  rw [h2, hV]
  have h3 := (Matrix.detRowAlternating (n := Fin n) (R := R)).toMultilinearMap.map_piecewise_smul (fun _ => x)
    (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) s
  refine Eq.trans h3 ?_
  rw [prod_const, smul_eq_mul]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
