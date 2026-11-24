-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.column_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:09.592547+00:00
-- url     : https://prove2.me/submissions/9683b224-5bde-4f54-a34b-c2d8e12439bf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : LatticeColumnOperatorBound := by
  intro O L _ _ _ M _ _ _ _ S U K c ϖ e1 w h1 h2 h3
  classical
  set ϖL := algebraMap O L ϖ with hϖL
  have hsm : ∀ (i k : ℕ) (x : M i), ϖ ^ k • x = (ϖL ^ k) • x := by
    intro i k x
    rw [hϖL, ← map_pow, algebraMap_smul]

  have hG : ∀ m (x : M 0), U m (chainK L M K m x) =
      (∏ j ∈ range m, (c j : L)) • chainK L M K m (U 0 x) := by
    intro m
    induction m with
    | zero => intro x; simp [chainK]
    | succ m ih =>
      intro x
      have h := LinearMap.congr_fun (h1 m) (chainK L M K m x)
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
      show U (m + 1) (K m (chainK L M K m x)) = _ • K m (chainK L M K m (U 0 x))
      rw [h, ih, map_smul, smul_smul, Finset.prod_range_succ, mul_comm]
  have hQ : ∀ m, ∀ s ∈ S 0, ((ϖL ^ (m * e1)) * ∏ j ∈ range m, (c j : L) ^ (m - j)) •
      chainK L M K m ((U 0 ^ m) s) ∈ S m := by
    intro m
    induction m with
    | zero => intro s hs; simpa [chainK] using hs
    | succ m ih =>
      intro s hs
      have h := h2 m _ (ih s hs)
      rw [hsm] at h
      have hstep : ∀ y, U (m + 1) (K m (chainK L M K m y)) =
          (∏ j ∈ range (m + 1), (c j : L)) • chainK L M K (m + 1) (U 0 y) := fun y => hG (m + 1) y
      rw [map_smul, map_smul, hstep, smul_smul, smul_smul] at h
      convert h using 2
      · have hP : ∏ j ∈ range (m + 1), (c j : L) ^ (m + 1 - j) =
            (∏ j ∈ range m, (c j : L) ^ (m - j)) * ∏ j ∈ range (m + 1), (c j : L) := by
          rw [Finset.prod_range_succ (fun j => (c j : L) ^ (m + 1 - j)),
            Finset.prod_range_succ (fun j => (c j : L))]
          have hh : ∏ j ∈ range m, (c j : L) ^ (m + 1 - j) =
              (∏ j ∈ range m, (c j : L) ^ (m - j)) * ∏ j ∈ range m, (c j : L) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun j hj => ?_
            rw [Finset.mem_range] at hj
            rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
          rw [hh, show m + 1 - m = 1 by omega, pow_one]
          ring
        rw [hP]
        ring
      · rw [pow_succ', Module.End.mul_apply]
  intro m s hs
  choose r hr using h3
  have hfin := (S m).smul_mem (∏ j ∈ range m, r j ^ (m - j)) (hQ m s hs)
  convert hfin using 1
  rw [hsm, ← algebraMap_smul L (∏ j ∈ range m, r j ^ (m - j)), smul_smul]
  congr 1
  rw [map_prod]
  simp only [map_pow, hr]
  rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
  have hh : (∏ j ∈ range m, ((((c j)⁻¹ : Lˣ) : L) * ϖL ^ w j) ^ (m - j)) *
      ∏ j ∈ range m, (c j : L) ^ (m - j) = ∏ j ∈ range m, ϖL ^ ((m - j) * w j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [mul_pow, mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul, ← pow_mul, mul_comm (w j)]
  rw [← hh]
  ring
end Formalism.HermitianLattices.RamifiedHeckeModels
