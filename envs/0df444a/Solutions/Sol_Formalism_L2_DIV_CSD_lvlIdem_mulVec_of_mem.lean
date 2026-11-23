-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.lvlIdem_mulVec_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:50.492045+00:00
-- url     : https://prove2.me/submissions/28f12e3c-d4f3-4a3e-b097-9a34f788c664

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_lvlIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Formalism.L2.DIV.CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin S.dim → K)
    (hx : x ∈ S.lvlPart r P ψ) : (S.gaMat r (lvlIdem P ψ)).mulVec x = x := by
  classical
  have hsum : ∀ (s : Finset P) (M : P → Matrix (Fin S.dim) (Fin S.dim) K),
      (∑ h ∈ s, M h).mulVec x = ∑ h ∈ s, (M h).mulVec x := by
    intro s M
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]
  have hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K),
      (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hx' : ∀ h : P, (S.actMat r (h : G)).mulVec x = ((ψ h : Kˣ) : K) • x := hx
  rw [S.gaMat_lvlIdem r P ψ, hsum]
  simp only [hsm, hx', smul_smul]
  rw [← Finset.sum_smul]
  have e : ∀ h : P, (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K) * ((ψ h : Kˣ) : K) = (Nat.card P : K)⁻¹ :=
    fun h => by rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]
end Formalism.L2.DIV.CSD
