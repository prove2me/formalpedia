-- Prove2me | solution 1 for CerednikDrinfeld.Omega.ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8677c4b1-d6c5-51f5-95cd-bb0d597db24f

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace C6Red

section OrdAt

theorem ordAt_eq_zero_of_apply_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (z : ↥(Omega.upperHalfPlane K₀ K))
    (hFz : (F : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0) : Omega.ordAt ϖ F z = 0 := by
  have hF : F ≠ 0 := fun h => hFz (by rw [h]; rfl)
  obtain ⟨G, hG, -⟩ := exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin F hF z
  by_contra hne
  apply hFz
  have := congrArg (fun H : ↥(Omega.holRing ϖ) => (H : ↥(Omega.upperHalfPlane K₀ K) → K) z) hG
  simp only [Subring.coe_mul, Subring.coe_pow, Pi.mul_apply, Pi.pow_apply, coordSub_apply_self,
    zero_pow hne, zero_mul] at this
  exact this

theorem one_le_ordAt_of_apply_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K))
    (hFz : (F : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0) : 1 ≤ Omega.ordAt ϖ F z := by
  have hb := bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hfin F hF z
  have h1 : Omega.coordSub ϖ z ^ 1 ∣ F := by
    rw [pow_one]; exact coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex F z hFz
  exact le_ordAt_of_pow_dvd ϖ F z h1 hb

end OrdAt

section Phi

noncomputable def phi {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K) (z : ↥(Omega.upperHalfPlane K₀ K))
    (x : FractionRing ↥(Omega.holRing ϖ)) : ℤ :=
  (Omega.ordAt ϖ (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).1 z : ℤ) -
    (Omega.ordAt ϖ ((IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).2 : ↥(Omega.holRing ϖ)) z : ℤ)

theorem phi_mk'
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (x : FractionRing ↥(Omega.holRing ϖ))
    (g : ↥(Omega.holRing ϖ)) (s : ↥(nonZeroDivisors ↥(Omega.holRing ϖ))) (hg : g ≠ 0)
    (hxe : x = IsLocalization.mk' (FractionRing ↥(Omega.holRing ϖ)) g s) :
    phi ϖ z x = (Omega.ordAt ϖ g z : ℤ) - (Omega.ordAt ϖ (s : ↥(Omega.holRing ϖ)) z : ℤ) := by
  set a := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).1 with ha
  set t := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).2 with ht
  have hsec : IsLocalization.mk' (FractionRing ↥(Omega.holRing ϖ)) a t = x := IsLocalization.mk'_sec _ x
  rw [hxe] at hsec
  obtain ⟨c, hc⟩ := (IsLocalization.eq).1 hsec

  have hc0 : (c : ↥(Omega.holRing ϖ)) ≠ 0 := nonZeroDivisors.ne_zero c.2
  have hcross : (s : ↥(Omega.holRing ϖ)) * a = (t : ↥(Omega.holRing ϖ)) * g := mul_left_cancel₀ hc0 hc
  have hs0 : (s : ↥(Omega.holRing ϖ)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ht0 : (t : ↥(Omega.holRing ϖ)) ≠ 0 := nonZeroDivisors.ne_zero t.2
  have ha0 : a ≠ 0 := by
    intro h0; apply hg
    have : (t : ↥(Omega.holRing ϖ)) * g = 0 := by rw [← hcross, h0, mul_zero]
    exact (mul_eq_zero.1 this).resolve_left ht0
  have hord := congrArg (fun F => (Omega.ordAt ϖ F z : ℤ)) hcross
  simp only [ordAt_mul K₀ K ϖ hrk hex hfin _ _ hs0 ha0, ordAt_mul K₀ K ϖ hrk hex hfin _ _ ht0 hg, Nat.cast_add] at hord
  show (Omega.ordAt ϖ a z : ℤ) - (Omega.ordAt ϖ (t : ↥(Omega.holRing ϖ)) z : ℤ) = _
  omega

theorem phi_mk
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (g h : ↥(Omega.holRing ϖ)) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors ↥(Omega.holRing ϖ)) :
    phi ϖ z (Localization.mk g ⟨h, hh⟩) = (Omega.ordAt ϖ g z : ℤ) - (Omega.ordAt ϖ h z : ℤ) :=
  phi_mk' K₀ K hrk ϖ hex hfin z _ g ⟨h, hh⟩ hg (Localization.mk_eq_mk'_apply _ _)

theorem sec_fst_ne_zero
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (x : FractionRing ↥(Omega.holRing ϖ)) (hx : x ≠ 0) :
    (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).1 ≠ 0 := by
  intro h0
  apply hx
  rw [← IsLocalization.mk'_sec (M := nonZeroDivisors ↥(Omega.holRing ϖ)) (FractionRing ↥(Omega.holRing ϖ)) x, h0,
    IsLocalization.mk'_zero]

theorem phi_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (x y : FractionRing ↥(Omega.holRing ϖ)) (hx : x ≠ 0) (hy : y ≠ 0) :
    phi ϖ z (x * y) = phi ϖ z x + phi ϖ z y := by
  have hax := sec_fst_ne_zero ϖ x hx
  have hay := sec_fst_ne_zero ϖ y hy
  set a := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).1
  set s := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) x).2
  set b := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) y).1
  set t := (IsLocalization.sec (nonZeroDivisors ↥(Omega.holRing ϖ)) y).2
  have hxe : x = IsLocalization.mk' (FractionRing ↥(Omega.holRing ϖ)) a s := (IsLocalization.mk'_sec _ x).symm
  have hye : y = IsLocalization.mk' (FractionRing ↥(Omega.holRing ϖ)) b t := (IsLocalization.mk'_sec _ y).symm
  have hxy : x * y = IsLocalization.mk' (FractionRing ↥(Omega.holRing ϖ)) (a * b) (s * t) := by
    rw [hxe, hye, IsLocalization.mk'_mul]
  rw [phi_mk' K₀ K hrk ϖ hex hfin z _ _ _ (mul_ne_zero hax hay) hxy,
    phi_mk' K₀ K hrk ϖ hex hfin z _ _ _ hax hxe, phi_mk' K₀ K hrk ϖ hex hfin z _ _ _ hay hye]
  have hs0 : ((s : ↥(nonZeroDivisors ↥(Omega.holRing ϖ))) : ↥(Omega.holRing ϖ)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ht0 : ((t : ↥(nonZeroDivisors ↥(Omega.holRing ϖ))) : ↥(Omega.holRing ϖ)) ≠ 0 := nonZeroDivisors.ne_zero t.2
  rw [Submonoid.coe_mul, ordAt_mul K₀ K ϖ hrk hex hfin _ _ hax hay, ordAt_mul K₀ K ϖ hrk hex hfin _ _ hs0 ht0]
  push_cast
  ring

theorem phi_one
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K)) :
    phi ϖ z 1 = 0 := by
  have h := phi_mul K₀ K hrk ϖ hex hfin z 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

theorem phi_inv
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (x : FractionRing ↥(Omega.holRing ϖ)) (hx : x ≠ 0) :
    phi ϖ z x⁻¹ = - phi ϖ z x := by
  have h := phi_mul K₀ K hrk ϖ hex hfin z x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, phi_one K₀ K hrk ϖ hex hfin z] at h
  omega

theorem phi_pow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (x : FractionRing ↥(Omega.holRing ϖ)) (hx : x ≠ 0) (n : ℕ) :
    phi ϖ z (x ^ n) = n * phi ϖ z x := by
  induction n with
  | zero => rw [pow_zero, phi_one K₀ K hrk ϖ hex hfin z]; simp
  | succ n ih => rw [pow_succ, phi_mul K₀ K hrk ϖ hex hfin z _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem phi_zpow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ K))
    (x : FractionRing ↥(Omega.holRing ϖ)) (hx : x ≠ 0) (n : ℤ) :
    phi ϖ z (x ^ n) = n * phi ϖ z x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, phi_pow K₀ K hrk ϖ hex hfin z x hx m]
  · rw [zpow_neg, zpow_natCast, phi_inv K₀ K hrk ϖ hex hfin z _ (pow_ne_zero _ hx),
      phi_pow K₀ K hrk ϖ hex hfin z x hx m]
    ring

end Phi

end C6Red

set_option maxHeartbeats 4000000 in
open C6Red in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ.map ρ)) w) : ℕ) : K) = 1)
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]

    (FC : Type) [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ))
    (pt : ↥(Omega.upperHalfPlane K₀ K) → Place K FC)
    (hpt : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0)))) :
    ∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (htame : ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℕ) : K) ≠ 0)
      (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
      (pt z).ord (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) *
          (Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℤ) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ) := by
  classical
  intro z htameZ g h hg hh hx
  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (HolRingOf.isDomain_iff ϖ ρ).1 inferInstance
  have hfinA := exists_finset_forall_v_sub_lt_of_finite_residueField K₀ K R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ

  let ιh : FC →+* FractionRing (Omega.HolRingOf ϖ ρ) := (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ).subtype.comp (eFC : FC →ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)).toRingHom
  have hι : ∀ x : FC, ιh x = ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) := fun x => rfl
  have hιinj : Function.Injective ιh :=
    (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ).subtype_injective.comp eFC.injective
  have hι0 : ∀ x : FC, ιh x = 0 ↔ x = 0 := fun x => map_eq_zero_iff ιh hιinj
  have hιsymm : ∀ (g₁ h₁ : Omega.HolRingOf ϖ ρ) (hh₁ : h₁ ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)) (hx₁ : Localization.mk g₁ ⟨h₁, hh₁⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
      ιh (eFC.symm ⟨Localization.mk g₁ ⟨h₁, hh₁⟩, hx₁⟩) = Localization.mk g₁ ⟨h₁, hh₁⟩ := by
    intro g₁ h₁ hh₁ hx₁; rw [hι, AlgEquiv.apply_symm_apply]

  have φmk : ∀ (g₁ h₁ : Omega.HolRingOf ϖ ρ) (hg₁ : g₁ ≠ 0) (hh₁ : h₁ ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      phi ϖ z ((Localization.mk g₁ ⟨h₁, hh₁⟩ : FractionRing (Omega.HolRingOf ϖ ρ))) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₁) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h₁) z : ℤ) :=
    fun g₁ h₁ hg₁ hh₁ => phi_mk K₀ K hrk ϖ hex hfinA z g₁ h₁ hg₁ hh₁
  have φpres : ∀ (g₁ h₁ : Omega.HolRingOf ϖ ρ) (hg₁ : g₁ ≠ 0) (hh₁ : h₁ ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      (show ↥(Omega.holRing ϖ) from h₁ : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
      phi ϖ z ((Localization.mk g₁ ⟨h₁, hh₁⟩ : FractionRing (Omega.HolRingOf ϖ ρ))) = (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₁) z : ℤ) := by
    intro g₁ h₁ hg₁ hh₁ hz
    rw [φmk g₁ h₁ hg₁ hh₁, ordAt_eq_zero_of_apply_ne_zero K₀ K hrk ϖ hex hfinA (show ↥(Omega.holRing ϖ) from h₁) z hz]
    simp

  have φnonneg : ∀ x : FC, x ∈ (pt z).toValuationSubring → x ≠ 0 → 0 ≤ phi ϖ z (ιh x) := by
    intro x hxm hx0
    obtain ⟨g₁, h₁, hh₁, hh₁z, hxe⟩ := (hpt.1 z x).1 hxm
    rw [← hι] at hxe
    have hg₁ : g₁ ≠ 0 := by
      intro h0; apply hx0
      apply (hι0 x).mp
      rw [hxe, h0, Localization.mk_zero]
    rw [hxe, φpres g₁ h₁ hg₁ hh₁ hh₁z]
    exact Int.natCast_nonneg _
  have φunit : ∀ u : (↥(pt z).toValuationSubring)ˣ, phi ϖ z (ιh ((u : ↥(pt z).toValuationSubring) : FC)) = 0 := by
    intro u
    have hu0 : ((u : ↥(pt z).toValuationSubring) : FC) ≠ 0 := by simp [ne_eq, ZeroMemClass.coe_eq_zero]
    have hui0 : (((u⁻¹ : (↥(pt z).toValuationSubring)ˣ) : ↥(pt z).toValuationSubring) : FC) ≠ 0 := by simp [ne_eq, ZeroMemClass.coe_eq_zero]
    have hu0' : ιh ((u : ↥(pt z).toValuationSubring) : FC) ≠ 0 := fun h0 => hu0 ((hι0 _).mp h0)
    have hui0' : ιh (((u⁻¹ : (↥(pt z).toValuationSubring)ˣ) : ↥(pt z).toValuationSubring) : FC) ≠ 0 := fun h0 => hui0 ((hι0 _).mp h0)
    have h1 := φnonneg _ (u : ↥(pt z).toValuationSubring).2 hu0
    have h2 := φnonneg _ ((u⁻¹ : (↥(pt z).toValuationSubring)ˣ) : ↥(pt z).toValuationSubring).2 hui0
    have hone : ιh ((u : ↥(pt z).toValuationSubring) : FC) * ιh (((u⁻¹ : (↥(pt z).toValuationSubring)ˣ) : ↥(pt z).toValuationSubring) : FC) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one, map_one]
    have h3 := phi_mul K₀ K hrk ϖ hex hfinA z _ _ hu0' hui0'
    erw [hone, phi_one K₀ K hrk ϖ hex hfinA z] at h3
    omega

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(pt z).toValuationSubring
  obtain ⟨g₀, h₀, hh₀, hh₀z, hπeq⟩ := (hpt.1 z (π : FC)).1 π.2
  rw [← hι] at hπeq
  have hπA0 : π ≠ 0 := hπ.ne_zero
  have hπ0 : ιh ((π : ↥(pt z).toValuationSubring) : FC) ≠ 0 := by
    intro h0; apply hπA0
    have := (hι0 _).mp h0
    rwa [ZeroMemClass.coe_eq_zero] at this
  have hg₀ : g₀ ≠ 0 := by
    intro h0; apply hπ0; rw [hπeq, h0, Localization.mk_zero]
  have hx₀ : Localization.mk g₀ ⟨h₀, hh₀⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ := by
    rw [← hπeq, hι]; exact (eFC _).2
  have hπeq' : ((π : ↥(pt z).toValuationSubring) : FC) = eFC.symm ⟨Localization.mk g₀ ⟨h₀, hh₀⟩, hx₀⟩ := by
    apply hιinj; rw [hιsymm, hπeq]
  have hnu : ((π : ↥(pt z).toValuationSubring) : FC) ∈ (pt z).toValuationSubring.nonunits := by
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hπ.not_isUnit
  have hg₀z : (show ↥(Omega.holRing ϖ) from g₀ : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 := by
    rw [hπeq'] at hnu
    exact ((hpt.2 z g₀ h₀ hh₀ hx₀ hh₀z).2).1 hnu
  have hφπ : phi ϖ z (ιh ((π : ↥(pt z).toValuationSubring) : FC)) = (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₀) z : ℤ) := by
    rw [hπeq, φpres g₀ h₀ hg₀ hh₀ hh₀z]
  have h1le : 1 ≤ Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₀) z :=
    one_le_ordAt_of_apply_eq_zero K₀ K hrk ϖ hex hfinA (show ↥(Omega.holRing ϖ) from g₀) hg₀ z hg₀z

  have hdiv := natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving K₀ K hrk hval R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex
    G ρ Γ htp hfin z htameZ g₀ h₀ hg₀ hh₀ hx₀
  rw [ordAt_eq_zero_of_apply_ne_zero K₀ K hrk ϖ hex hfinA (show ↥(Omega.holRing ϖ) from h₀) z hh₀z,
    Nat.cast_zero, sub_zero] at hdiv
  obtain ⟨g₁, h₁, hh₁, hx₁, hh₁z, hg₁, hord₁⟩ := exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
    K₀ K hrk hval R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex G ρ Γ htp hfin htame z

  have φfac : ∀ (x : FC) (hx0 : x ≠ 0), phi ϖ z (ιh x) = (pt z).ord x * (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₀) z : ℤ) := by
    intro x hx0
    obtain ⟨u, hu⟩ := (pt z).exists_unit_mul_zpow hx0 hπ
    have hu' := congrArg ιh hu
    rw [map_mul, map_zpow₀] at hu'
    erw [hu', phi_mul K₀ K hrk ϖ hex hfinA z _ _ (by
        intro h0; apply Units.ne_zero u; have := (hι0 _).mp h0; rwa [ZeroMemClass.coe_eq_zero] at this)
      (zpow_ne_zero _ hπ0),
      φunit u, zero_add, phi_zpow K₀ K hrk ϖ hex hfinA z _ hπ0, hφπ]

  have hx₁0 : eFC.symm ⟨Localization.mk g₁ ⟨h₁, hh₁⟩, hx₁⟩ ≠ 0 := by
    intro h0
    have h0' : (Localization.mk g₁ ⟨h₁, hh₁⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = 0 := by rw [← hιsymm g₁ h₁ hh₁ hx₁, h0, map_zero]
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at h0'
    obtain ⟨m, hm⟩ := h0'
    exact hg₁ ((mul_eq_zero.1 hm).resolve_left (nonZeroDivisors.ne_zero m.2))
  have e1 := φfac _ hx₁0
  rw [hιsymm, φpres g₁ h₁ hg₁ hh₁ hh₁z, hord₁] at e1

  set e : ℕ := Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) with he
  set m₀ : ℕ := Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g₀) z with hm₀
  have hem : (m₀ : ℤ) = e := by
    obtain ⟨k, hk⟩ := hdiv
    have he0 : (e : ℤ) ≠ 0 := by
      intro he0; rw [he0, zero_mul] at hk; omega
    have hk1 : (pt z).ord (eFC.symm ⟨Localization.mk g₁ ⟨h₁, hh₁⟩, hx₁⟩) * k = 1 := by
      have : (e : ℤ) * 1 = (e : ℤ) * ((pt z).ord (eFC.symm ⟨Localization.mk g₁ ⟨h₁, hh₁⟩, hx₁⟩) * k) := by
        rw [mul_one]; conv_lhs => rw [e1]
        rw [hk, mul_left_comm]
      exact (mul_left_cancel₀ he0 this).symm
    have hkpos : 0 ≤ k := by
      by_contra hneg
      have : (m₀ : ℤ) ≤ 0 := by rw [hk]; nlinarith [Int.natCast_nonneg e]
      omega
    have hk' : k = 1 := Int.eq_one_of_mul_eq_one_left hkpos hk1
    rw [hk, hk', mul_one]

  have hx0 : eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ≠ 0 := by
    intro h0
    have h0' : (Localization.mk g ⟨h, hh⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = 0 := by rw [← hιsymm g h hh hx, h0, map_zero]
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at h0'
    obtain ⟨m, hm⟩ := h0'
    exact hg ((mul_eq_zero.1 hm).resolve_left (nonZeroDivisors.ne_zero m.2))
  have e2 := φfac _ hx0
  rw [hιsymm, φmk g h hg hh, hem] at e2
  exact e2.symm

end S_CerednikDrinfeld_Omega_ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one (solution)
