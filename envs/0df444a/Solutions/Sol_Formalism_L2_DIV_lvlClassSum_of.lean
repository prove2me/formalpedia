-- Prove2me | solution 1 for Formalism.L2.DIV.lvlClassSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:55:27.72701+00:00
-- url     : https://prove2.me/submissions/974139e0-44da-4a77-a992-70f6c6f0b3d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_hform_smul
import Theorems.Thm_Formalism_L2_DIV_hform_cut
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
private theorem hform_eq_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) : hform M u v = star u ⬝ᵥ (M *ᵥ v) := by
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply,
    mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring
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
namespace Formalism.L2.DIV
theorem _root_.solution (h1 : ImESpec) : LvlClassSum := by
  intro K _ _ _ S G _ _ r P ψ
  have hEinj : Function.Injective (S.lvlE r P ψ).mulVec := (h1 K S.dim (S.gaMat r (lvlIdem P ψ))).1
  have hIinj : Function.Injective S.I := by
    intro x y hxy
    have h' : (S.basis.equivFun.symm x : S.Forms) = S.basis.equivFun.symm y := Subtype.ext hxy
    exact S.basis.equivFun.symm.injective h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hEinj (hIinj hxy)
  · intro x y
    unfold CSD.lvlH CSD.cutH
    rw [hform_smul, hform_cut, hform_eq_lemma, CSD.dot_H_lemma, Matrix.mulVec_smul, map_smul]
    unfold CSD.csum
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Pi.smul_apply, map_smul, smul_eq_mul, Nat.cast_mul, mul_inv]
    ring_nf
    rfl
  · first
    | rfl
    | (ext x; exact Iff.rfl)
  · first
    | rfl
    | (ext x; exact Iff.rfl)
end Formalism.L2.DIV
