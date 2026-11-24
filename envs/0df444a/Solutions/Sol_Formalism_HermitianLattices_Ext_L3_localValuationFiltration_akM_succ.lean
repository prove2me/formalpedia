-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localValuationFiltration.akM_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:50.146829+00:00
-- url     : https://prove2.me/submissions/34f8f988-3009-4f05-830c-af1d82af71c8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_card_rep_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_solve_matrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_trace_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localValuationFiltration
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)] {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.localValuationFiltration
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {c k : ℕ}
    (hDc : D ∉ 𝔭 ^ (c + 1)) (hk : 2 * c + 1 ≤ k) :
    Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = H.map (mkk K 𝔭 (k + 1))} =
      Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) *
        Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ k) //
          Xᴴ * H.map (mkk K 𝔭 k) * X = H.map (mkk K 𝔭 k)} := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have hj : k + 1 ≤ 2 * (k - c) := by omega
  have key := card_rep_succ (m := m) (r := m) hK h𝔭 H hH H hH hj (fun _ => True)
    (fun X Y _ => Iff.rfl) (fun X _ hX S hS hS' => by
      obtain ⟨Y, hY, hY'⟩ := exists_solve_matrix hF h𝔭 (by omega : c + 1 ≤ k) hD hDc hX
        (W := a • S) (fun i j => by
          rw [Matrix.smul_apply, smul_eq_mul]
          exact Ideal.mul_mem_left _ a (hS i j))
      refine ⟨Y, hY, fun i j => ?_⟩
      have e1 : Yᴴ * H * X - (a • S)ᴴ = (Xᴴ * H * Y - a • S)ᴴ := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      have h2 : (Yᴴ * H * X - (a • S)ᴴ) i j ∈ extP K 𝔭 ^ (k + 1) := by
        rw [e1, Matrix.conjTranspose_apply]
        exact conjO_mem_pow hF 𝔭 (k + 1) _ (hY' j i)
      have h3 : (a • S + (a • S)ᴴ - S) i j ∈ extP K 𝔭 ^ (k + 1) := by
        have e : (a • S + (a • S)ᴴ - S) i j =
            (a + star a - 1) * S i j + star a * ((Sᴴ - S) i j) := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
            Matrix.conjTranspose_apply, smul_eq_mul, star_mul']
          ring
        rw [e]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ (hS' i j))
      have e2 : (Xᴴ * H * Y + Yᴴ * H * X - S) i j = (Xᴴ * H * Y - a • S) i j +
          (Yᴴ * H * X - (a • S)ᴴ) i j + (a • S + (a • S)ᴴ - S) i j := by
        simp only [Matrix.sub_apply, Matrix.add_apply]
        ring
      rw [e2]
      exact Ideal.add_mem _ (Ideal.add_mem _ (hY' i j) h2) h3)
  simp only [true_and] at key
  have hN : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) := pow_pos (absNorm_pos h𝔭) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card m)) =
      Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) *
        Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) := by
    rw [two_mul, pow_add]
  apply Nat.eq_of_mul_eq_mul_right hN
  rw [key, e]
  ring
end Formalism.HermitianLattices.Ext.L3.localValuationFiltration
