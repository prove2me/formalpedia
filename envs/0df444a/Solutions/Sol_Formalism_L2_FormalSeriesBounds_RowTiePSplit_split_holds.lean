-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.split_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:35.601368+00:00
-- url     : https://prove2.me/submissions/e89b8529-8373-4e31-a507-948c35043089

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_exists_sep
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec1
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_commute_aeval
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_aeval_shift
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_X_sub_mul_basis
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_coeff_extract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution : SplitSt := by
  intro K _ _ O _ n ι _ _ M P em hPP hPM hinj hann v
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hP : P = 0 := by
      have h := hann 0
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_mul] at h
      exact h
    refine ⟨fun c => (hι.false c).elim, ?_, fun c => (hι.false c).elim⟩
    rw [hP, Matrix.zero_mulVec, Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨x0, hx0⟩ := exists_sep em hinj
  have hinjl : Set.InjOn (fun c => em c x0) (Finset.univ : Finset ι) := fun c _ c' _ h => by
    by_contra hne
    exact hx0 c c' hne h
  refine ⟨fun c => P *ᵥ (aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v), ?_, ?_⟩
  · rw [← Matrix.mulVec_sum, ← Matrix.sum_mulVec, ← map_sum, Lagrange.sum_basis hinjl Finset.univ_nonempty, map_one,
      Matrix.one_mulVec]
  intro c x
  set u := aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v with hu
  have hP0 : Commute P (M x0) := hPM x0

  have hXL : (X - Polynomial.C (em c x0)) * Lagrange.basis Finset.univ (fun c => em c x0) c =
      Polynomial.C (Lagrange.nodalWeight Finset.univ (fun c => em c x0) c) * ∏ c', (X - Polynomial.C (em c' x0)) :=
    X_sub_mul_basis (Finset.mem_univ c)
  have hE0 : (M x0 - algebraMap K _ (em c x0)) *
      (P * aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c)) = 0 := by
    have e1 : M x0 - algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) = aeval (M x0) (X - Polynomial.C (em c x0)) := by
      rw [map_sub, aeval_X, aeval_C]
    rw [e1, ← mul_assoc, ← (commute_aeval hP0 _).eq, mul_assoc, ← map_mul, hXL, map_mul, aeval_C, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, (commute_aeval hP0 _).eq, hann x0, mul_zero]
  have hw0 : M x0 *ᵥ (P *ᵥ u) = em c x0 • (P *ᵥ u) := by
    have h1 := congrArg (fun A => A *ᵥ v) hE0
    simp only [Matrix.zero_mulVec] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, alg_mulVec1, sub_eq_zero] at h1
    exact h1

  refine coeff_extract (M x) (P *ᵥ u) (fun c' => em c x0 - em c' x0) (fun c' => em c' x) c (sub_self _)
    (fun c' hc' => sub_ne_zero.2 (hx0 c c' (Ne.symm hc'))) fun t => ?_
  have hcx : Commute (M x0) ((t : Matrix (Fin n) (Fin n) K) * M x) := by
    refine ((Nat.cast_commute t (M x0)).symm).mul_right ?_
    show M x0 * M x = M x * M x0
    rw [← map_mul, ← map_mul, mul_comm]
  have h1 := congrArg (fun A => A *ᵥ u) (hann (x0 + (t : O) * x))
  simp only [Matrix.zero_mulVec] at h1
  rw [← Matrix.mulVec_mulVec, map_add, map_mul, map_natCast, aeval_shift _ _ hcx (em c x0) _ hw0] at h1
  have e2 : algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) + (t : Matrix (Fin n) (Fin n) K) * M x =
      aeval (M x) (Polynomial.C (em c x0) + Polynomial.C (t : K) * X) := by
    rw [map_add, map_mul, aeval_C, aeval_C, aeval_X, map_natCast]
  rw [e2, ← aeval_comp, prod_comp] at h1
  refine Eq.trans ?_ h1
  congr 2
  refine Finset.prod_congr rfl fun c' _ => ?_
  rw [sub_comp, X_comp, C_comp]
  simp only [map_add, map_mul, map_natCast, map_sub]
  ring
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
