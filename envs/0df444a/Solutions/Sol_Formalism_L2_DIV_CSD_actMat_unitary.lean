-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.actMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:18.517904+00:00
-- url     : https://prove2.me/submissions/d405b4eb-5cc7-4582-8e88-5adf4131be6c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_actMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
private theorem dot_H_lemma {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    (x y : Fin S.dim → K) : star x ⬝ᵥ (S.H *ᵥ y) = S.csum (S.I x) (S.I y) := by
  have hI : ∀ x : Fin S.dim → K, ∀ c, S.I x c = ∑ k, x k • (S.basis k : S.Cl → S.V) c := by
    intro x c
    show ((S.basis.equivFun.symm x : S.Forms) : S.Cl → S.V) c = _
    rw [Basis.equivFun_symm_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hp : ∀ (x y : Fin S.dim → K) (u w : Fin S.dim → S.V),
      S.pair (∑ k, x k • u k) (∑ l, y l • w l) = ∑ k, ∑ l, star (x k) * y l * S.pair (u k) (w l) := by
    intro x y u w
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold CSD.csum
  simp only [hI, hp]
  simp only [dotProduct, Matrix.mulVec, CSD.H, Matrix.of_apply, CSD.csum, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
  ring
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
end Formalism.L2.DIV.Test
end
end

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
theorem _root_.solution (hr : S.ActGood r) (t : G) :
    (S.actMat r t)ᴴ * S.H * S.actMat r t = S.H := by
  have Q := dot_H_lemma S
  have key : ∀ x y : Fin S.dim → K,
      star x ⬝ᵥ (((S.actMat r t)ᴴ * S.H * S.actMat r t) *ᵥ y) = star x ⬝ᵥ (S.H *ᵥ y) := by
    intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Q, Q,
      S.I_actMat r t, S.I_actMat r t]
    exact hr.unitary t _ _
  ext i j
  have hs : star (Pi.single i 1 : Fin S.dim → K) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  have := key (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this
end Formalism.L2.DIV.CSD
