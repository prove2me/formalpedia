-- Prove2me | solution 1 for FreyPackage.frey_exists_p_torsion_integral_abscissa_of_stable_line
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1b0df065-4981-5fe1-a2a5-fc6a95dabcab

import Mathlib.Algebra.Algebra.Rat
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial

section OrderHelpers

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private lemma slope_mul_lt_mul_of_lt_of_le {a b c d : Γ₀} (hab : a < b) (hcd : c ≤ d)
    (hd : d ≠ 0) : a * c < b * d :=
  lt_of_le_of_lt (mul_le_mul_right hcd a)
    (lt_of_le_of_ne (mul_le_mul_left hab.le d) fun h => hab.ne (mul_right_cancel₀ hd h))

private lemma slope_mul_lt_mul_of_le_of_lt {a b c d : Γ₀} (hab : a ≤ b) (hcd : c < d)
    (hb : b ≠ 0) : a * c < b * d :=
  lt_of_le_of_lt (mul_le_mul_left hab c)
    (lt_of_le_of_ne (mul_le_mul_right hcd.le b) fun h => hcd.ne (mul_left_cancel₀ hb h))

private lemma slope_one_lt_pow {M : Γ₀} (hM : 1 < M) {s : ℕ} (hs : s ≠ 0) : 1 < M ^ s := by
  induction s with
  | zero => exact absurd rfl hs
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hM
    · have hMn : 1 < M ^ n := ih (by omega)
      have hM0 : M ≠ 0 := (zero_lt_one.trans hM).ne'
      calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
        _ < M ^ n * M := slope_mul_lt_mul_of_lt_of_le hMn hM.le hM0
        _ = M ^ (n + 1) := (pow_succ M n).symm

private lemma slope_one_le_prod {s : Multiset Γ₀} (h : ∀ x ∈ s, 1 ≤ x) : 1 ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons]
    calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
      _ ≤ a * t.prod :=
        mul_le_mul' (h a (Multiset.mem_cons_self a t))
          (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

private lemma slope_one_lt_prod {s : Multiset Γ₀} (hne : s ≠ 0) (h : ∀ x ∈ s, 1 < x) :
    1 < s.prod := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, rfl⟩ : ∃ t, s = a ::ₘ t := ⟨s.erase a, (Multiset.cons_erase ha).symm⟩
  rw [Multiset.prod_cons]
  have h1a : 1 < a := h a (Multiset.mem_cons_self a t)
  have h1t : 1 ≤ t.prod := slope_one_le_prod fun x hx => (h x (Multiset.mem_cons_of_mem hx)).le
  have ht0 : t.prod ≠ 0 := (lt_of_lt_of_le zero_lt_one h1t).ne'
  calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
    _ < a * t.prod := slope_mul_lt_mul_of_lt_of_le h1a h1t ht0

end OrderHelpers

namespace Valuation
p2m_export "Valuation" "map_add_eq_of_lt_left ext map_sub map map_sub_le ne_zero_iff congr map_neg integer map_sum_lt map_add_lt map_sum_eq_of_lt"
p2m_open "Valuation"

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation K Γ₀)

private lemma _root_.Valuation.valuation_coeff_multisetProd_X_sub_C_le {t : Multiset K} {B : Γ₀}
    (ht : ∀ r ∈ t, v r ≤ B) (i : ℕ) :
    v (((t.map fun a => X - C a).prod).coeff i) ≤ B ^ (Multiset.card t - i) := by
  induction t using Multiset.induction generalizing i with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, Nat.zero_sub,
      pow_zero, Polynomial.coeff_one]
    split_ifs
    · simp only [v.map_one, le_refl]
    · simp only [v.map_zero, zero_le']
  | cons a t ih =>
    have hta : ∀ r ∈ t, v r ≤ B := fun r hr => ht r (Multiset.mem_cons_of_mem hr)
    have haB : v a ≤ B := ht a (Multiset.mem_cons_self a t)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases i with _ | j
    ·
      rw [Polynomial.mul_coeff_zero]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
      rw [map_mul, v.map_neg, Nat.sub_zero]
      calc v a * v (((t.map fun a => X - C a).prod).coeff 0)
          ≤ B * B ^ (Multiset.card t - 0) := mul_le_mul' haB (ih hta 0)
        _ = B ^ (Multiset.card t + 1) := by rw [Nat.sub_zero, ← pow_succ']
    ·
      have hexp : Multiset.card t + 1 - (j + 1) = Multiset.card t - j := by omega
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hexp]
      refine v.map_sub_le (ih hta j) ?_
      rw [map_mul]
      by_cases hj : j + 1 ≤ Multiset.card t
      · calc v a * v (((t.map fun a => X - C a).prod).coeff (j + 1))
            ≤ B * B ^ (Multiset.card t - (j + 1)) := mul_le_mul' haB (ih hta (j + 1))
          _ = B ^ (Multiset.card t - (j + 1) + 1) := by rw [← pow_succ']
          _ = B ^ (Multiset.card t - j) := by congr 1; omega
      · have hzero : ((t.map fun a => X - C a).prod).coeff (j + 1) = 0 := by
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
          omega
        rw [hzero, v.map_zero, mul_zero]
        exact zero_le'

p2m_export "Valuation" "valuation_coeff_multisetProd_X_sub_C_le"

private lemma _root_.Valuation.valuation_coeff_multisetProd_X_sub_C_lt {t : Multiset K} {B : Γ₀}
    (hB0 : B ≠ 0) (ht : ∀ r ∈ t, v r < B) {i : ℕ} (hi : i < Multiset.card t) :
    v (((t.map fun a => X - C a).prod).coeff i) < B ^ (Multiset.card t - i) := by
  induction t using Multiset.induction generalizing i with
  | empty => simp at hi
  | cons a t ih =>
    have hta : ∀ r ∈ t, v r < B := fun r hr => ht r (Multiset.mem_cons_of_mem hr)
    have htale : ∀ r ∈ t, v r ≤ B := fun r hr => (hta r hr).le
    have haB : v a < B := ht a (Multiset.mem_cons_self a t)
    rw [Multiset.card_cons] at hi
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases i with _ | j
    · rw [Polynomial.mul_coeff_zero]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
      rw [map_mul, v.map_neg, Nat.sub_zero]
      calc v a * v (((t.map fun a => X - C a).prod).coeff 0)
          < B * B ^ (Multiset.card t - 0) :=
            slope_mul_lt_mul_of_lt_of_le haB
              (v.valuation_coeff_multisetProd_X_sub_C_le htale 0)
              (pow_ne_zero _ hB0)
        _ = B ^ (Multiset.card t + 1) := by rw [Nat.sub_zero, ← pow_succ']
    · have hj : j < Multiset.card t := by omega
      have hexp : Multiset.card t + 1 - (j + 1) = Multiset.card t - j := by omega
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hexp]
      refine lt_of_le_of_lt (v.map_sub _ _) (max_lt ?_ ?_)
      · exact ih hta hj
      · rw [map_mul]
        calc v a * v (((t.map fun a => X - C a).prod).coeff (j + 1))
            < B * B ^ (Multiset.card t - (j + 1)) :=
              slope_mul_lt_mul_of_lt_of_le haB
                (v.valuation_coeff_multisetProd_X_sub_C_le htale (j + 1))
                (pow_ne_zero _ hB0)
          _ = B ^ (Multiset.card t - (j + 1) + 1) := by rw [← pow_succ']
          _ = B ^ (Multiset.card t - j) := by congr 1; omega

p2m_export "Valuation" "valuation_coeff_multisetProd_X_sub_C_lt"

private lemma _root_.Valuation.valuation_coeff_zero_multisetProd_X_sub_C (t : Multiset K) :
    v (((t.map fun a => X - C a).prod).coeff 0) = (t.map fun a => v a).prod := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map,
    map_multiset_prod (v : Valuation K Γ₀), Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    zero_sub, v.map_neg]

p2m_export "Valuation" "valuation_coeff_zero_multisetProd_X_sub_C"

private theorem _root_.Valuation.root_pow_natDegree_mul_leadingCoeff_eq_one {f : Polynomial K}
    (hsplit : Multiset.card f.roots = f.natDegree)
    (hcoeff : ∀ j, v (f.coeff j) ≤ 1)
    (hgap : ∀ j, v (f.coeff j) = 1 ∨ v (f.coeff j) ≤ v f.leadingCoeff)
    (hroots : ∀ r ∈ f.roots, 1 < v r)
    {r : K} (hr : r ∈ f.roots) :
    v (r ^ f.natDegree * f.leadingCoeff) = 1 := by
  classical

  have hf : f ≠ 0 := fun h => by simp [h] at hr
  have hπ0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hvπ0 : v f.leadingCoeff ≠ 0 := (Valuation.ne_zero_iff v).mpr hπ0
  have htne : f.roots ≠ 0 := fun h => by simp [h] at hr
  have hd1 : 1 ≤ f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exact absurd (Multiset.card_eq_zero.mp (hsplit.trans h0)) htne
    · exact h

  have hfact : Polynomial.C f.leadingCoeff * (f.roots.map fun a => X - C a).prod = f :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit

  obtain ⟨r₀, hr₀f, hr₀max⟩ : ∃ r₀ ∈ f.roots.toFinset, ∀ a ∈ f.roots.toFinset, v a ≤ v r₀ :=
    f.roots.toFinset.exists_max_image v (Multiset.toFinset_nonempty.mpr htne)
  have hr₀t : r₀ ∈ f.roots := Multiset.mem_toFinset.mp hr₀f
  have hmax : ∀ a ∈ f.roots, v a ≤ v r₀ := fun a ha =>
    hr₀max a (Multiset.mem_toFinset.mpr ha)
  have hM1 : 1 < v r₀ := hroots r₀ hr₀t
  have hM0 : v r₀ ≠ 0 := (zero_lt_one.trans hM1).ne'

  set u : Multiset K := f.roots.filter (fun a => v a = v r₀) with hu
  set w : Multiset K := f.roots.filter (fun a => ¬ v a = v r₀) with hw
  have huw : u + w = f.roots := Multiset.filter_add_not _ f.roots
  have hsw : Multiset.card u + Multiset.card w = f.natDegree := by
    rw [← Multiset.card_add, huw, hsplit]
  have hr₀u : r₀ ∈ u := Multiset.mem_filter.mpr ⟨hr₀t, rfl⟩
  have hs1 : Multiset.card u ≠ 0 := fun h =>
    absurd (Multiset.card_eq_zero.mp h ▸ hr₀u) (Multiset.notMem_zero r₀)
  have humem : ∀ a ∈ u, v a = v r₀ := fun a ha => (Multiset.mem_filter.mp ha).2
  have hwmem_lt : ∀ a ∈ w, v a < v r₀ := fun a ha =>
    lt_of_le_of_ne (hmax a (Multiset.mem_filter.mp ha).1) (Multiset.mem_filter.mp ha).2
  have hwmem_root : ∀ a ∈ w, a ∈ f.roots := fun a ha => (Multiset.mem_filter.mp ha).1

  have hgk : (f.roots.map fun a => X - C a).prod
      = (u.map fun a => X - C a).prod * (w.map fun a => X - C a).prod := by
    rw [← Multiset.prod_add, ← Multiset.map_add, huw]
  have hkmonic : ((w.map fun a => X - C a).prod).Monic :=
    Polynomial.monic_multisetProd_X_sub_C w
  have hkdeg : ((w.map fun a => X - C a).prod).natDegree = Multiset.card w :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card w
  have hgdeg : ((u.map fun a => X - C a).prod).natDegree = Multiset.card u :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card u

  have hg0 : v (((u.map fun a => X - C a).prod).coeff 0)
      = v r₀ ^ Multiset.card u := by
    rw [v.valuation_coeff_zero_multisetProd_X_sub_C u]
    have hrep : (u.map fun a => v a) = Multiset.replicate (Multiset.card u) (v r₀) :=
      Multiset.eq_replicate.mpr
        ⟨by rw [Multiset.card_map], fun b hb => by
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
          exact humem a ha⟩
    rw [hrep, Multiset.prod_replicate]

  have hcoeff_f : ∀ j, f.coeff j
      = f.leadingCoeff
        * ((u.map fun a => X - C a).prod * (w.map fun a => X - C a).prod).coeff j := by
    intro j
    conv_lhs => rw [← hfact, hgk]
    rw [Polynomial.coeff_C_mul]

  have hkey₀ : v (f.coeff (f.natDegree - Multiset.card u))
      = v f.leadingCoeff * v r₀ ^ Multiset.card u := by
    rw [hcoeff_f, map_mul]
    congr 1

    rw [Polynomial.coeff_mul]
    have hmem : ((0 : ℕ), f.natDegree - Multiset.card u)
        ∈ Finset.HasAntidiagonal.antidiagonal (f.natDegree - Multiset.card u) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add _)
    rw [← Finset.add_sum_erase _ _ hmem]
    have hterm : v ((((u.map fun a => X - C a).prod).coeff 0)
        * (((w.map fun a => X - C a).prod).coeff (f.natDegree - Multiset.card u)))
        = v r₀ ^ Multiset.card u := by
      have hwdeg : Multiset.card w = f.natDegree - Multiset.card u := by omega
      have htop : (((w.map fun a => X - C a).prod).coeff (f.natDegree - Multiset.card u)) = 1 := by
        rw [← hwdeg, ← hkdeg]
        exact hkmonic.coeff_natDegree
      rw [htop, mul_one, hg0]
    have hrest : v (∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal (f.natDegree - Multiset.card u)).erase
        (0, f.natDegree - Multiset.card u),
        (((u.map fun a => X - C a).prod).coeff ij.1)
          * (((w.map fun a => X - C a).prod).coeff ij.2))
        < v r₀ ^ Multiset.card u := by
      refine Valuation.map_sum_lt v (pow_ne_zero _ hM0) fun ij hij => ?_
      obtain ⟨hij_ne, hij_mem⟩ := Finset.mem_erase.mp hij
      have hij_sum : ij.1 + ij.2 = f.natDegree - Multiset.card u :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij_mem
      have hij1 : ij.1 ≠ 0 := by
        intro h0
        exact hij_ne (Prod.ext h0 (by omega))
      rw [map_mul]
      by_cases hbig : Multiset.card u < ij.1
      ·
        have : (((u.map fun a => X - C a).prod).coeff ij.1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; exact hbig)
        rw [this, v.map_zero, zero_mul]
        exact zero_lt_iff.mpr (pow_ne_zero _ hM0)
      · rw [not_lt] at hbig
        have hwdeg : Multiset.card w = f.natDegree - Multiset.card u := by omega
        have hij2 : ij.2 < Multiset.card w := by omega
        have h1 : v (((u.map fun a => X - C a).prod).coeff ij.1)
            ≤ v r₀ ^ (Multiset.card u - ij.1) :=
          v.valuation_coeff_multisetProd_X_sub_C_le (fun a ha => (humem a ha).le) ij.1
        have h2 : v (((w.map fun a => X - C a).prod).coeff ij.2)
            < v r₀ ^ (Multiset.card w - ij.2) :=
          v.valuation_coeff_multisetProd_X_sub_C_lt hM0 hwmem_lt hij2
        calc v (((u.map fun a => X - C a).prod).coeff ij.1)
              * v (((w.map fun a => X - C a).prod).coeff ij.2)
            < v r₀ ^ (Multiset.card u - ij.1) * v r₀ ^ (Multiset.card w - ij.2) :=
              slope_mul_lt_mul_of_le_of_lt h1 h2 (pow_ne_zero _ hM0)
          _ = v r₀ ^ (Multiset.card u - ij.1 + (Multiset.card w - ij.2)) := (pow_add _ _ _).symm
          _ = v r₀ ^ Multiset.card u := by congr 1; omega
    rw [Valuation.map_add_eq_of_lt_left v (hterm ▸ hrest), hterm]

  have hkey : v f.leadingCoeff * v r₀ ^ Multiset.card u = 1 := by
    rcases hgap (f.natDegree - Multiset.card u) with h1 | h2
    · rw [← hkey₀, h1]
    · exfalso
      rw [hkey₀] at h2

      have hcancel : v r₀ ^ Multiset.card u ≤ 1 := by
        have h3 := mul_le_mul_right h2 (v f.leadingCoeff)⁻¹
        rwa [← mul_assoc, inv_mul_cancel₀ hvπ0, one_mul] at h3
      exact absurd hcancel (not_le.mpr (slope_one_lt_pow hM1 hs1))

  have hwzero : w = 0 := by
    by_contra hwne
    have hconst : v (f.coeff 0) = (w.map fun a => v a).prod := by
      rw [hcoeff_f, map_mul, Polynomial.mul_coeff_zero, map_mul, hg0,
        v.valuation_coeff_zero_multisetProd_X_sub_C w, ← mul_assoc, hkey, one_mul]
    have hgt : 1 < (w.map fun a => v a).prod := by
      refine slope_one_lt_prod (by simpa using hwne) fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      exact hroots a (hwmem_root a ha)
    exact absurd (hconst ▸ hcoeff 0) (not_le.mpr hgt)

  have hsd : Multiset.card u = f.natDegree := by
    have : Multiset.card w = 0 := by rw [hwzero, Multiset.card_zero]
    omega
  have hru : r ∈ u := by
    have : r ∈ u + w := huw ▸ hr
    rwa [hwzero, add_zero] at this
  rw [map_mul, v.map_pow, humem r hru, ← hsd, mul_comm]
  exact hkey

p2m_export "Valuation" "root_pow_natDegree_mul_leadingCoeff_eq_one"
end Valuation

namespace ValuationSubring
p2m_export "ValuationSubring" "ext zero_mem nonunits mem_nonunits_iff valuation_le_one_iff valuation LiesOverPrime"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.mul_mem_nonunits_of_mem {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

p2m_export "ValuationSubring" "mul_mem_nonunits_of_mem"

private theorem _root_.ValuationSubring.valuation_intCast_eq_one_of_not_dvd {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) : A.valuation ((n : ℤ) : L) = 1 := by
  have hle : A.valuation ((n : ℤ) : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have hnu : ((n : ℤ) : L) ∈ A.nonunits := A.mem_nonunits_iff.mpr hlt
  have hqirr : Irreducible ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨u, v, huv⟩ := hqirr.coprime_iff_not_dvd.mpr hn
  have hone : (1 : L) = (u : L) * (q : L) + (v : L) * ((n : ℤ) : L) := by
    have := congrArg (fun z : ℤ => (z : L)) huv
    push_cast at this
    rw [← this]
  have hlt1 : A.valuation (1 : L) < 1 := by
    rw [hone]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact A.mem_nonunits_iff.mp (A.mul_mem_nonunits_of_mem (intCast_mem A u) hA)
    · exact A.mem_nonunits_iff.mp (A.mul_mem_nonunits_of_mem (intCast_mem A v) hnu)
  rw [map_one] at hlt1
  exact lt_irrefl _ hlt1

p2m_export "ValuationSubring" "valuation_intCast_eq_one_of_not_dvd"

private theorem _root_.ValuationSubring.valuation_intCast_eq_one_or_le {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    (m : ℤ) : A.valuation (m : L) = 1 ∨ A.valuation (m : L) ≤ A.valuation (q : L) := by
  by_cases hdvd : (q : ℤ) ∣ m
  · right
    obtain ⟨k, rfl⟩ := hdvd
    have hcast : (((q : ℤ) * k : ℤ) : L) = (q : L) * (k : L) := by push_cast; ring
    rw [hcast, map_mul]
    calc A.valuation (q : L) * A.valuation (k : L)
        ≤ A.valuation (q : L) * 1 :=
          mul_le_mul_right ((A.valuation_le_one_iff _).mpr (intCast_mem A k)) _
      _ = A.valuation (q : L) := mul_one _
  · left
    exact A.valuation_intCast_eq_one_of_not_dvd hq hA hdvd

p2m_export "ValuationSubring" "valuation_intCast_eq_one_or_le"

private theorem _root_.ValuationSubring.exists_valuation_intCast_eq_pow {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    ∀ (m : ℤ), m ≠ 0 → ∃ a : ℕ, A.valuation (m : L) = A.valuation (q : L) ^ a := by
  intro m
  induction h : m.natAbs using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    intro hm0
    by_cases hdvd : (q : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      have hm'0 : m' ≠ 0 := fun h0 => hm0 (by rw [h0, mul_zero])
      have hq2 : 1 < q := hq.one_lt
      have hlt : m'.natAbs < k := by
        rw [← h, Int.natAbs_mul, Int.natAbs_natCast]
        have hpos : 0 < m'.natAbs := Int.natAbs_pos.mpr hm'0
        nlinarith
      obtain ⟨a, ha⟩ := ih m'.natAbs hlt m' rfl hm'0
      refine ⟨a + 1, ?_⟩
      push_cast
      rw [map_mul, ha, pow_succ, mul_comm]
    · exact ⟨0, by rw [pow_zero]; exact A.valuation_intCast_eq_one_of_not_dvd hq hA hdvd⟩

p2m_export "ValuationSubring" "exists_valuation_intCast_eq_pow"

private theorem _root_.ValuationSubring.exists_valuation_ratCast_mul_pow_eq_pow [CharZero L] {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (c : ℚ) (hc : c ≠ 0) :
    ∃ a b : ℕ, A.valuation (c : L) * A.valuation (q : L) ^ b = A.valuation (q : L) ^ a := by
  obtain ⟨a, ha⟩ := A.exists_valuation_intCast_eq_pow hq hA c.num (Rat.num_ne_zero.mpr hc)
  obtain ⟨b, hb⟩ := A.exists_valuation_intCast_eq_pow hq hA (c.den : ℤ)
    (by exact_mod_cast c.den_nz)
  refine ⟨a, b, ?_⟩
  have hden0 : ((c.den : ℤ) : L) ≠ 0 := by exact_mod_cast c.den_nz
  have hc' : (c : L) * ((c.den : ℤ) : L) = (c.num : L) := by
    rw [Rat.cast_def]
    push_cast
    rw [div_mul_cancel₀]
    exact_mod_cast c.den_nz
  rw [← hb, ← ha, ← map_mul, hc']

p2m_export "ValuationSubring" "exists_valuation_ratCast_mul_pow_eq_pow"
end ValuationSubring

namespace FreyPackage
p2m_export "FreyPackage" "freyCurve_discriminant hp_odd habc0 freyCurveInt freyCurve c hb2 p a hp5 b ha4 pp"
p2m_open "FreyPackage"

private theorem _root_.FreyPackage.freyCurveInt_map_eq (P : FreyPackage) :
    (P.freyCurveInt).map (algebraMap ℤ ℚ) = P.freyCurve := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2     := by norm_num
          _       ∣ P.b ^ 2   := pow_dvd_pow_of_dvd two_dvd_b 2
          _       ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, if_neg]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4     := by norm_num
        _        ∣ P.b ^ 4   := pow_dvd_pow_of_dvd two_dvd_b 4
        _        ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _        ∣ _         := Int.dvd_mul_left _ _
  · rfl

p2m_export "FreyPackage" "freyCurveInt_map_eq"
open WeierstrassCurve in

private theorem _root_.FreyPackage.coeff_preΨ'_freyCurve_baseChange (P : FreyPackage) (n j : ℕ) :
    (((P.freyCurve).baseChange (AlgebraicClosure ℚ)).preΨ' n).coeff j
      = ((((P.freyCurveInt).preΨ' n).coeff j : ℤ) : AlgebraicClosure ℚ) := by
  have hcurve : (P.freyCurve).baseChange (AlgebraicClosure ℚ)
      = (P.freyCurveInt).map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    rw [← P.freyCurveInt_map_eq]
    show (P.freyCurveInt).map
        ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ℤ ℚ))
      = (P.freyCurveInt).map (Int.castRingHom (AlgebraicClosure ℚ))
    exact congrArg (fun φ : ℤ →+* AlgebraicClosure ℚ => (P.freyCurveInt).map φ)
      (Subsingleton.elim _ _)
  rw [hcurve, WeierstrassCurve.map_preΨ', Polynomial.coeff_map, eq_intCast]

p2m_export "FreyPackage" "coeff_preΨ'_freyCurve_baseChange"
end FreyPackage

section Main

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

local notation "Kb" => AlgebraicClosure ℚ

noncomputable def absc {F : Type*} [Field F] {W : Affine F} : W.Point → F
  | .zero => 0
  | .some x _ _ => x

theorem solution (P : FreyPackage) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∃ (t : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) (x y : AlgebraicClosure ℚ) (h : (P.freyCurve⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), (t : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = Point.some x y h ∧ x ∈ A := by
  classical
  by_contra hcon
  push Not at hcon

  have hp : P.p.Prime := P.pp
  have hp5 := P.hp5
  have hodd : Odd P.p := P.hp_odd
  have hneven : ¬ Even P.p := Nat.not_even_iff_odd.mpr hodd
  have hpK : ((P.p : ℕ) : Kb) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  haveI hE : P.freyCurve.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, P.freyCurve_discriminant, isUnit_iff_ne_zero]
    have h : ((P.a : ℚ) * P.b * P.c) ≠ 0 := by exact_mod_cast P.habc0
    exact div_ne_zero (pow_ne_zero _ h) (by norm_num)
  haveI hEK : (P.freyCurve⁄Kb).IsElliptic :=
    inferInstanceAs (((P.freyCurve).map (algebraMap ℚ Kb)).IsElliptic)

  have hvp1 : A.valuation ((P.p : ℕ) : Kb) < 1 := A.mem_nonunits_iff.mp hA
  have hvp0 : A.valuation ((P.p : ℕ) : Kb) ≠ 0 := (Valuation.ne_zero_iff _).mpr hpK
  have hvp0' : 0 < A.valuation ((P.p : ℕ) : Kb) := zero_lt_iff.mpr hvp0

  set f : Polynomial Kb := (P.freyCurve⁄Kb).preΨ' P.p with hf
  set d : ℕ := (P.p ^ 2 - 1) / 2 with hd
  have hdeg : f.natDegree = d := by
    rw [hf, (P.freyCurve⁄Kb).natDegree_preΨ' hpK, if_neg hneven]
  have hlead : f.leadingCoeff = ((P.p : ℕ) : Kb) := by
    rw [hf, (P.freyCurve⁄Kb).leadingCoeff_preΨ' hpK, if_neg hneven]
  have hf0 : f ≠ 0 := (P.freyCurve⁄Kb).preΨ'_ne_zero hpK

  have mem_tor : ∀ {Q : (P.freyCurve⁄Kb).Point},
      Q ∈ Submodule.torsionBy ℤ (P.freyCurve⁄Kb).Point P.p ↔ P.p • Q = 0 := by
    intro Q
    rw [Submodule.mem_torsionBy_iff]
    exact ⟨fun h => by simpa [Nat.cast_smul_eq_nsmul] using h,
      fun h => by simpa [Nat.cast_smul_eq_nsmul] using h⟩

  have hroots : ∀ r ∈ f.roots, 1 < A.valuation r := by
    intro r hr
    have hev : f.eval r = 0 := (Polynomial.mem_roots hf0).mp hr

    set b₁ : Kb := (P.freyCurve⁄Kb).a₁ * r + (P.freyCurve⁄Kb).a₃ with hb₁
    set c₁ : Kb := -(r ^ 3 + (P.freyCurve⁄Kb).a₂ * r ^ 2 + (P.freyCurve⁄Kb).a₄ * r
      + (P.freyCurve⁄Kb).a₆) with hc₁
    obtain ⟨y, hy⟩ : ∃ y : Kb, IsRoot (C 1 * X ^ 2 + C b₁ * X + C c₁) y :=
      IsAlgClosed.exists_root _ (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
    have heq : (P.freyCurve⁄Kb).toAffine.Equation r y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have := hy
      simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at this
      rw [hb₁, hc₁] at this
      linear_combination this
    have hns : (P.freyCurve⁄Kb).toAffine.Nonsingular r y :=
      ((P.freyCurve⁄Kb).toAffine.equation_iff_nonsingular).mp heq

    have htor : P.p • (Point.some r y hns : (P.freyCurve⁄Kb).Point) = 0 :=
      (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi (P.freyCurve⁄Kb) hodd
        hns).mpr hev
    have hnotA : r ∉ A := hcon ⟨_, mem_tor.mpr htor⟩ r y hns rfl
    exact not_le.mp fun hle => hnotA ((A.valuation_le_one_iff _).mp hle)

  have hslope : ∀ r ∈ f.roots,
      A.valuation r ^ d * A.valuation ((P.p : ℕ) : Kb) = 1 := by
    intro r hr
    have hmain := A.valuation.root_pow_natDegree_mul_leadingCoeff_eq_one (f := f)
      (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits f))
      (fun j => by
        rw [hf, P.coeff_preΨ'_freyCurve_baseChange]
        exact (A.valuation_le_one_iff _).mpr (intCast_mem A _))
      (fun j => by
        rw [hlead, hf, P.coeff_preΨ'_freyCurve_baseChange]
        exact A.valuation_intCast_eq_one_or_le hp hA _)
      hroots hr
    rwa [hdeg, hlead, map_mul, map_pow] at hmain

  obtain ⟨T₀, hT₀N, hT₀0⟩ := (Submodule.ne_bot_iff N).mp hbot
  obtain ⟨x₀, y₀, h₀, hT₀eq⟩ : ∃ (x₀ y₀ : Kb) (h₀ : (P.freyCurve⁄Kb).toAffine.Nonsingular x₀ y₀),
      (T₀ : (P.freyCurve⁄Kb).Point) = Point.some x₀ y₀ h₀ := by
    rcases hT : (T₀ : (P.freyCurve⁄Kb).Point) with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd (Subtype.ext hT) hT₀0
    · exact ⟨x₀, y₀, h₀, rfl⟩
  have hx₀root : x₀ ∈ f.roots := by
    refine (Polynomial.mem_roots hf0).mpr ?_
    have htor : P.p • (T₀ : (P.freyCurve⁄Kb).Point) = 0 := mem_tor.mp T₀.2
    rw [hT₀eq] at htor
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi (P.freyCurve⁄Kb)
      hodd h₀).mp htor
  have hx₀A : x₀ ∉ A := hcon T₀ x₀ y₀ h₀ hT₀eq
  have hx₀0 : x₀ ≠ 0 := fun h => hx₀A (h ▸ A.zero_mem)
  have hvx₀ : A.valuation x₀ ^ d * A.valuation ((P.p : ℕ) : Kb) = 1 := hslope x₀ hx₀root
  have hvx₀0 : A.valuation x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0

  have hcardT : Nat.card (Submodule.torsionBy ℤ (P.freyCurve⁄Kb).Point P.p) = P.p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := Kb) P.freyCurve hpK
  haveI hfinT : Finite (Submodule.torsionBy ℤ (P.freyCurve⁄Kb).Point P.p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero _ hp.ne_zero)
  have hcardN : Nat.card N ≤ P.p := by
    have hdvd : Nat.card N ∣ P.p ^ 2 := by
      rw [← hcardT]
      exact AddSubgroup.card_addSubgroup_dvd_card N.toAddSubgroup
    obtain ⟨z, hzN⟩ : ∃ z : Submodule.torsionBy ℤ (P.freyCurve⁄Kb).Point P.p, z ∉ N := by
      by_contra hall
      push Not at hall
      exact htop (Submodule.eq_top_iff'.mpr hall)
    have hlt : Nat.card N < P.p ^ 2 := by
      rw [← hcardT]
      exact Finite.card_subtype_lt (p := fun z => z ∈ N) hzN
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact (lt_irrefl _) (hkeq ▸ hlt)
    have hk1 : k ≤ 1 := by omega
    rw [hkeq]
    calc P.p ^ k ≤ P.p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = P.p := pow_one _

  haveI : Fintype N := Fintype.ofFinite N
  set S : Finset Kb := ((Finset.univ : Finset N).filter (fun T : N => T ≠ 0)).image
    (fun T : N => absc (W := P.freyCurve⁄Kb) T.1.1) with hS
  have hScard : S.card ≤ P.p - 1 := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.filter_ne' Finset.univ (0 : N), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  have hx₀S : x₀ ∈ S := by
    rw [hS, Finset.mem_image]
    refine ⟨⟨T₀, hT₀N⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro h0
      exact hT₀0 (congrArg Subtype.val h0)
    · show absc T₀.1 = x₀
      have : T₀.1 = Point.some x₀ y₀ h₀ := hT₀eq
      rw [this]
      rfl

  have absc_smul : ∀ (σ : Kb ≃ₐ[ℚ] Kb) (Q : (P.freyCurve⁄Kb).Point), absc (σ • Q) = σ (absc Q) := by
    intro σ Q
    rcases Q with _ | ⟨x, y, h⟩
    · show absc (σ • (0 : (P.freyCurve⁄Kb).Point)) = σ 0
      rw [_root_.map_zero]
      rfl
    · rfl
  have hSstab : ∀ σ : Kb ≃ₐ[ℚ] Kb, S.image σ = S := by
    intro σ
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨s', hs', rfl⟩ := hs
      rw [hS, Finset.mem_image] at hs' ⊢
      obtain ⟨T, hT, rfl⟩ := hs'
      have hT0 : T ≠ 0 := (Finset.mem_filter.mp hT).2
      refine ⟨⟨σ • T.1, hN σ _ T.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro h0
        apply hT0
        have h1 : σ • T.1 = 0 := congrArg Subtype.val h0
        have h2 : T.1 = 0 := by
          have := congrArg (fun z => σ⁻¹ • z) h1
          simpa only [inv_smul_smul, smul_zero] using this
        exact Subtype.ext h2
      · exact absc_smul σ T.1.1
    · rw [Finset.card_image_of_injective _ σ.injective]

  set g : Polynomial Kb := ∏ s ∈ S, (X - C s) with hg
  have hgmonic : g.Monic := monic_prod_X_sub_C id S
  have hgdeg : g.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card S id
  have hgx₀ : g.eval x₀ = 0 := by
    rw [hg, eval_prod]
    exact Finset.prod_eq_zero hx₀S (by simp)
  have hgmap : ∀ σ : Kb ≃ₐ[ℚ] Kb, g.map (σ : Kb →+* Kb) = g := by
    intro σ
    rw [hg, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    have hinj : ∀ x ∈ S, ∀ y ∈ S, (σ : Kb →+* Kb) x = (σ : Kb →+* Kb) y → x = y :=
      fun x _ y _ hxy => σ.injective hxy
    rw [← Finset.prod_image (g := (σ : Kb →+* Kb)) (f := fun s => X - C s) hinj]
    have : S.image (σ : Kb →+* Kb) = S := by
      have h := hSstab σ
      convert h using 2
      rfl
    rw [this]
  haveI : IsGalois ℚ Kb := by
    have h : @IsGalois ℚ _ Kb _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hcoeffQ : ∀ i, ∃ c : ℚ, (c : Kb) = g.coeff i := by
    intro i
    have hfix : ∀ σ : Kb ≃ₐ[ℚ] Kb, σ (g.coeff i) = g.coeff i := by
      intro σ
      have := congrArg (fun q : Polynomial Kb => q.coeff i) (hgmap σ)
      simp only [Polynomial.coeff_map] at this
      exact this
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (g.coeff i)).mpr
      hfix
    exact ⟨c, by rw [← hc]; exact (eq_ratCast _ c).symm⟩

  have hdS : S.card < d := by
    obtain ⟨k, hk⟩ := hodd
    have hsq : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have hd' : d = 2 * k ^ 2 + 2 * k := by
      rw [hd, hk, hsq, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have hk2 : 2 ≤ k := by omega
    have h1 : S.card ≤ 2 * k := by omega
    have h2 : 2 * k < 2 * k ^ 2 + 2 * k := by nlinarith
    omega

  have hterm_ne : ∀ i j : ℕ, i < j → j ≤ S.card → g.coeff i ≠ 0 → g.coeff j ≠ 0 →
      A.valuation (g.coeff i * x₀ ^ i) ≠ A.valuation (g.coeff j * x₀ ^ j) := by
    intro i j hij hjS hci hcj heqv
    obtain ⟨ci, hci'⟩ := hcoeffQ i
    obtain ⟨cj, hcj'⟩ := hcoeffQ j
    have hci0 : ci ≠ 0 := by rintro rfl; apply hci; rw [← hci']; push_cast; rfl
    have hcj0 : cj ≠ 0 := by rintro rfl; apply hcj; rw [← hcj']; push_cast; rfl
    obtain ⟨ai, bi, hvi⟩ := A.exists_valuation_ratCast_mul_pow_eq_pow hp hA ci hci0
    obtain ⟨aj, bj, hvj⟩ := A.exists_valuation_ratCast_mul_pow_eq_pow hp hA cj hcj0
    rw [← hci', ← hcj', map_mul, map_mul, map_pow, map_pow] at heqv

    set vq := A.valuation ((P.p : ℕ) : Kb) with hvq
    set vx := A.valuation x₀ with hvx
    set vi := A.valuation (ci : Kb) with hvi'
    set vj := A.valuation (cj : Kb) with hvj'

    obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
    have he0 : 0 < e := by omega
    have hed : e < d := by omega
    have heqv' : vi = vj * vx ^ e := by
      rw [pow_add, mul_comm (vx ^ i) (vx ^ e), ← mul_assoc] at heqv
      exact mul_right_cancel₀ (pow_ne_zero i hvx₀0) heqv

    have E1 : vq ^ (ai + bj) = vq ^ (aj + bi) * vx ^ e := by
      rw [pow_add, pow_add, ← hvi, ← hvj, heqv']
      simp only [mul_assoc, mul_comm, mul_left_comm]

    have hxd : vx ^ d * vq = 1 := hvx₀
    have E2 : vq ^ ((ai + bj) * d + e) = vq ^ ((aj + bi) * d) := by
      have h1 : (vq ^ (ai + bj)) ^ d * vq ^ e = (vq ^ (aj + bi) * vx ^ e) ^ d * vq ^ e :=
        by rw [E1]
      rw [← pow_mul, ← pow_add] at h1
      rw [h1, mul_pow, ← pow_mul, mul_assoc,
        show (vx ^ e) ^ d * vq ^ e = (vx ^ d * vq) ^ e by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e d],
        hxd, one_pow, mul_one]
    have E3 : (ai + bj) * d + e = (aj + bi) * d :=
      (pow_right_strictAnti₀ hvp0' hvp1).injective E2

    rcases Nat.lt_or_ge (ai + bj) (aj + bi) with hlt | hge
    · have h3 : (ai + bj + 1) * d ≤ (aj + bi) * d := Nat.mul_le_mul_right d hlt
      rw [Nat.succ_mul] at h3
      linarith
    · have h3 : (aj + bi) * d ≤ (ai + bj) * d := Nat.mul_le_mul_right d hge
      linarith

  set I : Finset ℕ := (Finset.range (g.natDegree + 1)).filter (fun i => g.coeff i ≠ 0) with hI
  have hnI : g.natDegree ∈ I := by
    rw [hI, Finset.mem_filter]
    exact ⟨Finset.self_mem_range_succ _, by rw [hgmonic.coeff_natDegree]; exact one_ne_zero⟩
  obtain ⟨j, hjI, hjmax⟩ := I.exists_max_image (fun i => A.valuation (g.coeff i * x₀ ^ i))
    ⟨_, hnI⟩
  have hjcoeff : g.coeff j ≠ 0 := (Finset.mem_filter.mp hjI).2
  have hjle : j ≤ S.card := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hjI).1
    omega
  have hvj0 : A.valuation (g.coeff j * x₀ ^ j) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (mul_ne_zero hjcoeff (pow_ne_zero _ hx₀0))
  have hsum : A.valuation (g.eval x₀) = A.valuation (g.coeff j * x₀ ^ j) := by
    rw [Polynomial.eval_eq_sum_range]
    refine Valuation.map_sum_eq_of_lt _ ?_ ?_
    · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (Finset.mem_filter.mp hjI).1; omega)
    · intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      by_cases hci : g.coeff i = 0
      · rw [hci, zero_mul, _root_.map_zero]
        exact zero_lt_iff.mpr hvj0
      · have hiI : i ∈ I := Finset.mem_filter.mpr ⟨hi.1, hci⟩
        refine lt_of_le_of_ne (hjmax i hiI) ?_
        have hile : i ≤ S.card := by
          have := Finset.mem_range.mp hi.1
          omega
        rcases lt_or_gt_of_ne hi.2 with hlt | hgt
        · exact hterm_ne i j hlt hjle hci hjcoeff
        · exact (hterm_ne j i hgt hile hjcoeff hci).symm
  rw [hgx₀, _root_.map_zero] at hsum
  exact hvj0 hsum.symm

end Main

end S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line
end P2MW
export P2MW.S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line (solution)
