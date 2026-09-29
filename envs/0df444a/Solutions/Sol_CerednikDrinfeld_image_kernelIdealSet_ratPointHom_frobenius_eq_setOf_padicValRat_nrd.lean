-- Prove2me | solution 1 for CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8b791194-3d3f-5b80-94de-1cbddc8948cc

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Theorems.Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
import Theorems.Thm_WeierstrassCurve_exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace FrobeniusKernelIdealPinned
namespace Poly

variable {k : Type*} [Field k]

theorem wronskian_C_mul (a : k) (u v : k[X]) :
    wronskian (C a * u) (C a * v) = C a ^ 2 * wronskian u v := by
  simp only [wronskian, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem wronskian_map {S : Type*} [Field S] (f : k →+* S) (u v : k[X]) :
    wronskian (u.map f) (v.map f) = (wronskian u v).map f := by
  simp only [wronskian, derivative_map, Polynomial.map_mul, Polynomial.map_sub]

theorem derivative_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f : k[X]) : derivative (expand k (p ^ j) f) = 0 := by
  rw [derivative_expand]
  have : ((p ^ j : ℕ) : k[X]) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k[X] p, zero_pow hj]
  rw [this, zero_mul, mul_zero]

theorem wronskian_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f g : k[X]) : wronskian (expand k (p ^ j) f) (expand k (p ^ j) g) = 0 := by
  simp only [wronskian, derivative_expand_pow_eq_zero p hj, mul_zero, zero_mul, sub_self]

theorem ne_C_mul_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) (c : k) : u ≠ C c * v := by
  intro huc
  have hvu : v ∣ u := ⟨C c, by rw [huc, mul_comm]⟩
  have hunit : IsUnit v := huv.isUnit_of_dvd' hvu (dvd_refl v)
  have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  have hu0 : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [huc]; exact (natDegree_C_mul_le _ _).trans_eq hv0
  omega

theorem eval_ne_zero_of_isCoprime {u v : k[X]} (huv : IsCoprime u v) {x : k} (hv : v.eval x = 0) :
    u.eval x ≠ 0 := by
  intro hu
  obtain ⟨a, b, hab⟩ := huv
  have := congr_arg (eval x) hab
  simp [hu, hv] at this

theorem exists_C_mul_of_mul_eq_mul {u₁ v₁ u₂ v₂ : k[X]} (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (heq : u₁ * v₂ = u₂ * v₁) :
    ∃ c : k, c ≠ 0 ∧ u₂ = C c * u₁ ∧ v₂ = C c * v₁ := by
  have d12 : u₁ ∣ u₂ := h₁.dvd_of_dvd_mul_right ⟨v₂, by rw [heq]⟩
  have d21 : u₂ ∣ u₁ := h₂.dvd_of_dvd_mul_right ⟨v₁, by rw [← heq]⟩
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd d12 d21
  obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  refine ⟨c, hc.ne_zero, by rw [← hw, ← hcw, mul_comm], ?_⟩
  have : u₁ * v₂ = u₁ * (C c * v₁) := by
    rw [heq, ← hw, ← hcw]; ring
  exact mul_left_cancel₀ hu₁ this

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exists_expand_wronskian_ne_zero {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) :
    ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
      IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  suffices H : ∀ n : ℕ, ∀ u v : k[X], max u.natDegree v.natDegree = n → IsCoprime u v →
      0 < max u.natDegree v.natDegree →
      ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
        IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 from
    H _ u v rfl huv h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hn huv hpos
    by_cases hw : wronskian u v ≠ 0
    · exact ⟨0, u, v, by simp, by simp, huv, hpos, hw⟩
    push Not at hw
    obtain ⟨hdu, hdv⟩ := huv.wronskian_eq_zero_iff.mp hw
    set u₁ := contract p u
    set v₁ := contract p v
    have hu : u = expand k p u₁ := (expand_contract p hdu hp).symm
    have hv : v = expand k p v₁ := (expand_contract p hdv hp).symm
    have hcop : IsCoprime u₁ v₁ := by
      rw [hu, hv, isCoprime_expand hp] at huv; exact huv
    have hdeg_u : u.natDegree = u₁.natDegree * p := by rw [hu, natDegree_expand]
    have hdeg_v : v.natDegree = v₁.natDegree * p := by rw [hv, natDegree_expand]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hmax : max u.natDegree v.natDegree = max u₁.natDegree v₁.natDegree * p := by
      rw [hdeg_u, hdeg_v, Nat.mul_max_mul_right]
    have hpos₁ : 0 < max u₁.natDegree v₁.natDegree := by
      rcases Nat.eq_zero_or_pos (max u₁.natDegree v₁.natDegree) with h0 | h0
      · rw [hmax, h0, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    have hlt : max u₁.natDegree v₁.natDegree < n := by
      rw [← hn, hmax]
      exact lt_mul_of_one_lt_right hpos₁ hp1
    obtain ⟨e, u₀, v₀, hu₀, hv₀, hc₀, hpos₀, hw₀⟩ := ih _ hlt u₁ v₁ rfl hcop hpos₁
    refine ⟨e + 1, u₀, v₀, ?_, ?_, hc₀, hpos₀, hw₀⟩
    · rw [hu, hu₀, expand_expand, pow_succ']
    · rw [hv, hv₀, expand_expand, pow_succ']

theorem expand_exponent_le {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : b ≤ a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_contra hlt
  push Not at hlt
  have hu₁ : u₁ ≠ 0 := by
    intro h0; apply hw₁
    have : c₁ = 0 := expand_injective (pow_pos hp a) (by rw [← ha, h0, map_zero])
    rw [this, wronskian_zero_left]
  have hu₂ : u₂ ≠ 0 := by
    intro h0; apply hw₂
    have : c₂ = 0 := expand_injective (pow_pos hp b) (by rw [← hb, h0, map_zero])
    rw [this, wronskian_zero_left]
  obtain ⟨c, hc, hcu, hcv⟩ := exists_C_mul_of_mul_eq_mul h₁ h₂ hu₁ hu₂ heq

  obtain ⟨j, hj⟩ : ∃ j, b = a + j := ⟨b - a, by omega⟩
  have hj0 : j ≠ 0 := by omega
  have e1 : C c * c₁ = expand k (p ^ j) c₂ := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha, ← hcu, hb, hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have e2 : C c * c₁' = expand k (p ^ j) c₂' := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha', ← hcv, hb', hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have hz : wronskian (C c * c₁) (C c * c₁') = 0 := by
    rw [e1, e2, wronskian_expand_pow_eq_zero p hj0]
  rw [wronskian_C_mul] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hc (by simpa using h)
  · exact hw₁ h

theorem expand_exponent_unique {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : a = b :=
  le_antisymm
    (expand_exponent_le p h₂ h₁ (by rw [mul_comm, heq, mul_comm]) hb hb' ha ha' hw₂ hw₁)
    (expand_exponent_le p h₁ h₂ heq ha ha' hb hb' hw₁ hw₂)

end CharP

noncomputable def hom (m : ℕ) (u v s : k[X]) : k[X] :=
  ∑ i ∈ Finset.range (m + 1), C (s.coeff i) * u ^ i * v ^ (m - i)

theorem eval_hom {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x x' : k}
    (hx : x' * v.eval x = u.eval x) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval x' := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hs), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← hx, mul_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  ring

theorem eval_hom_div {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x : k} (hv : v.eval x ≠ 0) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval (u.eval x / v.eval x) :=
  eval_hom hs (div_mul_cancel₀ _ hv)

theorem comp_core [IsAlgClosed k] {u v s t : k[X]} (huv : IsCoprime u v)
    (hu : 0 < max u.natDegree v.natDegree) (hw : wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : wronskian s t ≠ 0) :
    IsCoprime (hom (max s.natDegree t.natDegree) u v s) (hom (max s.natDegree t.natDegree) u v t) ∧
      0 < max (hom (max s.natDegree t.natDegree) u v s).natDegree
        (hom (max s.natDegree t.natDegree) u v t).natDegree ∧
      wronskian (hom (max s.natDegree t.natDegree) u v s)
        (hom (max s.natDegree t.natDegree) u v t) ≠ 0 :=
  Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero huv hu hw hst hs hw'
    (fun x hx => eval_hom_div (le_max_left _ _) hx) (fun x hx => eval_hom_div (le_max_right _ _) hx)

section Twist

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem eval_pow_eq_eval_map_iterateFrobenius (u : k[X]) (y : k) (j : ℕ) :
    (u.eval y) ^ (p ^ j) = (u.map (iterateFrobenius k p j)).eval (y ^ (p ^ j)) := by
  rw [eval_map, ← iterateFrobenius_def, ← iterateFrobenius_def p j y, eval₂_at_apply]

theorem natDegree_map' (u : k[X]) (f : k →+* k) : (u.map f).natDegree = u.natDegree :=
  natDegree_map_eq_of_injective f.injective u

theorem wronskian_map_ne_zero_iff {u v : k[X]} (f : k →+* k) :
    wronskian (u.map f) (v.map f) ≠ 0 ↔ wronskian u v ≠ 0 := by
  rw [wronskian_map, Ne, Polynomial.map_eq_zero_iff f.injective]

end Twist

section Comp

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem exists_comp_expand {u v s t a₁ a₂ b₁ b₂ : k[X]} {a b : ℕ}
    (hu : u = expand k (p ^ b) b₁) (hv : v = expand k (p ^ b) b₂)
    (hs : s = expand k (p ^ a) a₁) (ht : t = expand k (p ^ a) a₂)
    (hbc : IsCoprime b₁ b₂) (hbpos : 0 < max b₁.natDegree b₂.natDegree) (hbw : wronskian b₁ b₂ ≠ 0)
    (hac : IsCoprime a₁ a₂) (hapos : 0 < max a₁.natDegree a₂.natDegree) (haw : wronskian a₁ a₂ ≠ 0) :
    ∃ U₀ V₀ : k[X], IsCoprime U₀ V₀ ∧ 0 < max U₀.natDegree V₀.natDegree ∧ wronskian U₀ V₀ ≠ 0 ∧
      ∀ x : k, v.eval x ≠ 0 → t.eval (u.eval x / v.eval x) ≠ 0 →
        (expand k (p ^ (a + b)) V₀).eval x ≠ 0 ∧
        (expand k (p ^ (a + b)) U₀).eval x / (expand k (p ^ (a + b)) V₀).eval x =
          s.eval (u.eval x / v.eval x) / t.eval (u.eval x / v.eval x) := by
  set σ := iterateFrobenius k p a
  set b₁' := b₁.map σ
  set b₂' := b₂.map σ
  have hbc' : IsCoprime b₁' b₂' := (isCoprime_map σ).mpr hbc
  have hbpos' : 0 < max b₁'.natDegree b₂'.natDegree := by
    rwa [natDegree_map' b₁ σ, natDegree_map' b₂ σ]
  have hbw' : wronskian b₁' b₂' ≠ 0 := (wronskian_map_ne_zero_iff σ).mpr hbw
  set m := max a₁.natDegree a₂.natDegree
  obtain ⟨hc, hpos, hw⟩ := comp_core hbc' hbpos' hbw' hac hapos haw
  refine ⟨hom m b₁' b₂' a₁, hom m b₁' b₂' a₂, hc, hpos, hw, fun x hvx htx => ?_⟩
  set z := x ^ (p ^ (a + b)) with hz
  set w := u.eval x / v.eval x with hw_def
  have hz' : z = (x ^ (p ^ b)) ^ (p ^ a) := by rw [hz, ← pow_mul, ← pow_add, add_comm]
  have e₁ : b₁'.eval z = (u.eval x) ^ (p ^ a) := by
    rw [hz', hu, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have e₂ : b₂'.eval z = (v.eval x) ^ (p ^ a) := by
    rw [hz', hv, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have hb₂z : b₂'.eval z ≠ 0 := by rw [e₂]; exact pow_ne_zero _ hvx
  have hwz : w ^ (p ^ a) * b₂'.eval z = b₁'.eval z := by
    rw [e₁, e₂, hw_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hvx)]
  have hs' : s.eval w = a₁.eval (w ^ (p ^ a)) := by rw [hs, expand_eval]
  have ht' : t.eval w = a₂.eval (w ^ (p ^ a)) := by rw [ht, expand_eval]
  have hU : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₁)).eval x = (b₂'.eval z) ^ m * s.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_left _ _) hwz, hs']
  have hV : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₂)).eval x = (b₂'.eval z) ^ m * t.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_right _ _) hwz, ht']
  have hVne : (b₂'.eval z) ^ m * t.eval w ≠ 0 := mul_ne_zero (pow_ne_zero _ hb₂z) htx
  refine ⟨by rwa [hV], ?_⟩
  rw [hU, hV, mul_div_mul_left _ _ (pow_ne_zero _ hb₂z)]

end Comp

theorem eq_of_eval_eq_off_finite [Infinite k] {f g : k[X]} {S : Set k} (hS : S.Finite)
    (h : ∀ x, x ∉ S → f.eval x = g.eval x) : f = g := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Sᶜ)
  · intro x hx; exact h x hx
  · exact hS.infinite_compl

theorem finite_fibre {u v : k[X]} (huv : IsCoprime u v) (h : 0 < max u.natDegree v.natDegree)
    (c : k) : {x : k | u.eval x = c * v.eval x}.Finite := by
  have hne : u - C c * v ≠ 0 := sub_ne_zero.mpr (ne_C_mul_of_isCoprime_of_pos huv h c)
  refine (finite_setOf_isRoot hne).subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  simp [IsRoot, hx]

end FrobeniusKernelIdealPinned.Poly

namespace FrobeniusKernelIdealPinned

open WeierstrassCurve WeierstrassCurve.Affine Polynomial FrobeniusKernelIdealPinned.Poly

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

omit [DecidableEq k] in
theorem exists_nonsingular (W : WeierstrassCurve k) [W.IsElliptic] (x : k) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set q : k[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    with hq
  have hdeg : q.degree = 2 := by
    rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; decide)
  refine ⟨y, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  simp only [hq, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy
  linear_combination hy

section XPair

variable {W₁ W₂ W₃ : WeierstrassCurve k}

def IsXPair (f : W₁.toAffine.Point → W₂.toAffine.Point) (u v : k[X]) (B : Set k) : Prop :=
  IsCoprime u v ∧ 0 < max u.natDegree v.natDegree ∧ B.Finite ∧
    ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'),
        f (.some x y h) = .some x' y' h' ∧ x' * v.eval x = u.eval x

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem IsXPair.eval_ne_zero {f : W₁.toAffine.Point → W₂.toAffine.Point} {u v : k[X]} {B : Set k}
    (hf : IsXPair f u v B) {x : k} (hx : x ∉ B) : v.eval x ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x', y', h', -, hx'⟩ := hf.2.2.2 x y hy hx
  intro hv
  rw [hv, mul_zero] at hx'
  exact eval_ne_zero_of_isCoprime hf.1 hv hx'.symm

theorem IsXPair.mul_eq_mul {f : W₁.toAffine.Point → W₂.toAffine.Point} {u₁ v₁ u₂ v₂ : k[X]}
    {B₁ B₂ : Set k} (h₁ : IsXPair f u₁ v₁ B₁) (h₂ : IsXPair f u₂ v₂ B₂) :
    u₁ * v₂ = u₂ * v₁ := by
  apply eq_of_eval_eq_off_finite (h₁.2.2.1.union h₂.2.2.1)
  intro x hx
  rw [Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x₁, y₁, h₁', e₁, r₁⟩ := h₁.2.2.2 x y hy hx.1
  obtain ⟨x₂, y₂, h₂', e₂, r₂⟩ := h₂.2.2.2 x y hy hx.2
  rw [e₁] at e₂
  obtain ⟨rfl, -⟩ := (Affine.Point.some.injEq _ _ _ _ _ _).mp e₂
  rw [eval_mul, eval_mul, ← r₁, ← r₂]; ring

omit [W₂.IsElliptic] in

theorem exists_isXPair {α : W₁.toAffine.Point →+ W₂.toAffine.Point} [W₂.IsElliptic]
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ u v B, IsXPair α u v B := by
  obtain ⟨u, v, B, huv, hB, hrep⟩ := WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet k W₁ W₂ hα hα0
  have hlt : v.natDegree < u.natDegree :=
    WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α huv hB hrep
  exact ⟨u, v, B, huv, lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlt) (le_max_left _ _), hB,
    hrep⟩

end XPair

section Height

variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {W₁ W₂ W₃ : WeierstrassCurve k}

def HasHeight (f : W₁.toAffine.Point → W₂.toAffine.Point) (e : ℕ) : Prop :=
  ∃ (u v : k[X]) (B : Set k) (u₀ v₀ : k[X]), IsXPair f u v B ∧
    u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
    IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem hasHeight_unique {f : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (ha : HasHeight p f a) (hb : HasHeight p f b) : a = b := by
  obtain ⟨u₁, v₁, B₁, c₁, c₁', h₁, hu₁, hv₁, -, -, hw₁⟩ := ha
  obtain ⟨u₂, v₂, B₂, c₂, c₂', h₂, hu₂, hv₂, -, -, hw₂⟩ := hb
  exact expand_exponent_unique p h₁.1 h₂.1 (h₁.mul_eq_mul h₂) hu₁ hv₁ hu₂ hv₂ hw₁ hw₂

omit [W₂.IsElliptic] in
theorem exists_hasHeight [W₂.IsElliptic] {α : W₁.toAffine.Point →+ W₂.toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ e, HasHeight p α e := by
  obtain ⟨u, v, B, h⟩ := exists_isXPair hα hα0
  obtain ⟨e, u₀, v₀, hu, hv, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p h.1 h.2.1
  exact ⟨e, u, v, B, u₀, v₀, h, hu, hv, hc, hpos, hw⟩

theorem HasHeight.comp {f : W₂.toAffine.Point → W₃.toAffine.Point}
    {g : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (hf : HasHeight p f a) (hg : HasHeight p g b) : HasHeight p (f ∘ g) (a + b) := by
  obtain ⟨s, t, Bf, a₁, a₂, hfx, hs, ht, hac, hapos, haw⟩ := hf
  obtain ⟨u, v, Bg, b₁, b₂, hgx, hu, hv, hbc, hbpos, hbw⟩ := hg
  obtain ⟨U₀, V₀, hc, hpos, hw, hsem⟩ :=
    exists_comp_expand p hu hv hs ht hbc hbpos hbw hac hapos haw
  have hp : (p ^ (a + b)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine ⟨expand k (p ^ (a + b)) U₀, expand k (p ^ (a + b)) V₀,
    Bg ∪ ⋃ c ∈ Bf, {x : k | u.eval x = c * v.eval x}, U₀, V₀, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, hc, hpos, hw⟩
  · exact (isCoprime_expand hp).mpr hc
  · rw [natDegree_expand, natDegree_expand, Nat.mul_max_mul_right]
    exact Nat.mul_pos hpos (Nat.pos_of_ne_zero hp)
  · exact hgx.2.2.1.union (hfx.2.2.1.biUnion fun c _ => finite_fibre hgx.1 hgx.2.1 c)
  · intro x y h hx
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hx
    obtain ⟨hxg, hxf⟩ := hx
    obtain ⟨x', y', h', e₁, r₁⟩ := hgx.2.2.2 x y h hxg
    have hvx : v.eval x ≠ 0 := hgx.eval_ne_zero hxg
    have hx' : x' = u.eval x / v.eval x := by rw [← r₁, mul_div_cancel_right₀ _ hvx]
    have hx'B : x' ∉ Bf := fun hmem => hxf x' hmem (by rw [← r₁])
    obtain ⟨x'', y'', h'', e₂, r₂⟩ := hfx.2.2.2 x' y' h' hx'B
    have htx : t.eval x' ≠ 0 := hfx.eval_ne_zero hx'B
    obtain ⟨hV, hUV⟩ := hsem x hvx (by rwa [← hx'])
    refine ⟨x'', y'', h'', by rw [Function.comp_apply, e₁, e₂], ?_⟩
    rw [← hx'] at hUV
    rw [← eq_div_iff hV, hUV, eq_div_iff htx, r₂]

theorem hasHeight_id : HasHeight p (id : W₁.toAffine.Point → W₁.toAffine.Point) 0 := by
  refine ⟨X, 1, ∅, X, 1, ⟨isCoprime_one_right, by simp, Set.finite_empty, ?_⟩, by simp, by simp,
    isCoprime_one_right, by simp, ?_⟩
  · intro x y h _
    exact ⟨x, y, h, rfl, by simp⟩
  · simp [wronskian]

end Height

section HomSet

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented K W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -Polynomial.X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty,
    fun x y h _ => ?_⟩
  have e0 : evalEvalBC K (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC K (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC K (-Polynomial.X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange K).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

variable {K}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) : -α ∈ rationalHomSet K W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet K W₁ W₂ W₂ hα
    (Or.inr (isRationallyRepresented_neg_id K W₂))
  have e : (-(AddMonoidHom.id _)).comp α = -α := AddMonoidHom.ext fun P => rfl
  rwa [e] at h

variable [IsAlgClosed K]

theorem sub_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) (hβ : β ∈ rationalHomSet K W₁ W₂) :
    α - β ∈ rationalHomSet K W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet K W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet K W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet K W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet K W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact sub_mem_rationalHomSet ih hα

variable (K) in

noncomputable def homSubring (W : WeierstrassCurve F) [W.IsElliptic] :
    Subring (AddMonoid.End (W.baseChange K).toAffine.Point) where
  carrier := rationalHomSet K W W
  mul_mem' ha hb := WeierstrassCurve.comp_mem_rationalHomSet K W W W hb ha
  one_mem' := id_mem_rationalHomSet K W
  add_mem' ha hb := WeierstrassCurve.add_mem_rationalHomSet K W W ha hb
  zero_mem' := zero_mem_rationalHomSet K W W
  neg_mem' hα := neg_mem_rationalHomSet hα

theorem mem_rationalHomSet_of_mem_rationalEndSubring (W : WeierstrassCurve F) [W.IsElliptic]
    {α : AddMonoid.End (W.baseChange K).toAffine.Point} (hα : α ∈ rationalEndSubring K W) :
    (α : (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point) ∈ rationalHomSet K W W := by
  have : rationalEndSubring K W ≤ homSubring K W := Subring.closure_le.mpr (fun x hx => hx)
  exact this hα

end HomSet

section MulN

variable (W : WeierstrassCurve k) [W.IsElliptic]

theorem ΨSq_ne_zero {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  intro h0
  have hc := WeierstrassCurve.isCoprime_Phi_PsiSq W n
  rw [h0, isCoprime_zero_right] at hc
  have := natDegree_eq_zero_of_isUnit hc
  rw [WeierstrassCurve.natDegree_Φ] at this
  simp [hn] at this

theorem isXPair_zsmul {n : ℤ} (hn : n ≠ 0) :
    IsXPair (fun P : W.toAffine.Point => n • P) (W.Φ n) (W.ΨSq n) {x | (W.ΨSq n).IsRoot x} := by
  refine ⟨WeierstrassCurve.isCoprime_Phi_PsiSq W n, ?_, finite_setOf_isRoot (ΨSq_ne_zero W hn), ?_⟩
  · rw [WeierstrassCurve.natDegree_Φ]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  · intro x y h hx
    simp only [Set.mem_setOf_eq, IsRoot.def] at hx
    have hψ : (W.ψ n).evalEval x y ≠ 0 := by
      intro h0
      have := WeierstrassCurve.Affine.evalEval_psi_sq W h.1 n
      rw [h0] at this
      exact hx (by simpa using this.symm)
    obtain ⟨y', h', e⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W h hψ
    exact ⟨_, y', h', e, div_mul_cancel₀ _ hx⟩

theorem exists_zsmul_ne_zero {n : ℤ} (hn : n ≠ 0) : ∃ P : W.toAffine.Point, n • P ≠ 0 := by
  have hpair := isXPair_zsmul W hn
  obtain ⟨x, hx⟩ := hpair.2.2.1.infinite_compl.nonempty
  obtain ⟨y, hy⟩ := exists_nonsingular W x
  obtain ⟨x', y', h', e1, -⟩ := hpair.2.2.2 x y hy hx
  refine ⟨.some x y hy, ?_⟩
  have e1' : n • (Affine.Point.some x y hy : W.toAffine.Point) = .some x' y' h' := e1
  rw [e1']
  exact Affine.Point.some_ne_zero h'

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem wronskian_Φ_ΨSq_eq_zero : wronskian (W.Φ p) (W.ΨSq p) = 0 := by
  have h := WeierstrassCurve.Psi2Sq_mul_wronskian_sq W (p : ℤ)
  have hp : ((p : ℤ) : k) = 0 := by rw [Int.cast_natCast]; exact CharP.cast_eq_zero k p
  rw [hp, zero_pow two_ne_zero, C_0, zero_mul] at h
  have h2 := (mul_eq_zero.mp h).resolve_left (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W)
  have h3 : derivative (W.Φ p) * W.ΨSq p - W.Φ p * derivative (W.ΨSq p) = 0 := pow_eq_zero_iff
    two_ne_zero |>.mp h2
  rw [wronskian, ← neg_eq_zero, neg_sub', sub_neg_eq_add]
  linear_combination h3

theorem exists_hasHeight_mulP :
    ∃ π₀ : ℕ, 1 ≤ π₀ ∧ HasHeight p (fun P : W.toAffine.Point => (p : ℤ) • P) π₀ := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hcop := WeierstrassCurve.isCoprime_Phi_PsiSq W (p : ℤ)
  obtain ⟨hd1, hd2⟩ := hcop.wronskian_eq_zero_iff.mp (wronskian_Φ_ΨSq_eq_zero W p)
  have e1 : W.Φ p = expand k p (contract p (W.Φ p)) := (expand_contract p hd1 hp).symm
  have e2 : W.ΨSq p = expand k p (contract p (W.ΨSq p)) := (expand_contract p hd2 hp).symm
  have hcop' : IsCoprime (contract p (W.Φ p)) (contract p (W.ΨSq p)) := by
    rw [e1, e2, isCoprime_expand hp] at hcop; exact hcop
  have hpos' : 0 < max (contract p (W.Φ p)).natDegree (contract p (W.ΨSq p)).natDegree := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have hdeg : (W.Φ p).natDegree = (contract p (W.Φ p)).natDegree * p := by
      conv_lhs => rw [e1]
      rw [natDegree_expand]
    rw [WeierstrassCurve.natDegree_Φ] at hdeg
    by_contra h0
    push Not at h0
    have : (contract p (W.Φ (p : ℤ))).natDegree = 0 := by omega
    rw [this, zero_mul] at hdeg
    simp [hp] at hdeg
  obtain ⟨e, r₁, r₂, hr₁, hr₂, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p hcop' hpos'
  refine ⟨e + 1, Nat.le_add_left 1 e, _, _, _, r₁, r₂, isXPair_zsmul W hpz, ?_, ?_, hc, hpos, hw⟩
  · rw [e1, hr₁, expand_expand, pow_succ']
  · rw [e2, hr₂, expand_expand, pow_succ']

end MulN

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable abbrev frobTwist (W : WeierstrassCurve k) : WeierstrassCurve k := W.map (frobenius k p)

scoped instance instIsEllipticFrobTwist (W : WeierstrassCurve k) [W.IsElliptic] : (frobTwist p W).IsElliptic := by
  unfold frobTwist; infer_instance

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve k) [W.IsElliptic] : (W.baseChange k).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular_iff (W : WeierstrassCurve k) (x y : k) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) ↔ W.toAffine.Nonsingular x y := by
  have := Affine.map_nonsingular W.toAffine (f := frobenius k p) (frobenius_inj k p) x y
  simpa only [frobenius_def] using this

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) :=
  (frob_nonsingular_iff p W x y).mpr h

noncomputable def frobPt (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (frobTwist p W).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (x ^ p) (y ^ p) (frob_nonsingular p W h)
  map_zero' := rfl
  map_add' := by
    have hf : ∀ z : k, frobenius k p z = z ^ p := frobenius_def p
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
      have h2 : y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p) := by
        rw [hxy.right, ← hf, ← hf, ← hf, Affine.map_negY]
      rw [Affine.Point.add_of_Y_eq (congr_arg (· ^ p) hxy.left) h2]
    · have hxy' : ¬ (x₁ ^ p = x₂ ^ p ∧
          y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
        rintro ⟨e1, e2⟩
        apply hxy
        refine ⟨frobenius_inj k p (by rw [hf, hf]; exact e1), frobenius_inj k p ?_⟩
        rw [hf, hf, e2, ← hf, ← hf, Affine.map_negY, hf]
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      simp only [Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addX]
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addY]

theorem frobPt_some (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    frobPt p W (.some x y h) = .some (x ^ p) (y ^ p) (frob_nonsingular p W h) := rfl

theorem frobPt_injective (W : WeierstrassCurve k) : Function.Injective (frobPt p W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [frobPt_some, frobPt_some, Affine.Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have hx : x₁ = x₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e1)
    have hy : y₁ = y₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e2)
    subst hx hy
    rfl

theorem frobPt_surjective (W : WeierstrassCurve k) : Function.Surjective (frobPt p W) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rintro (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq u hp
    obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq v hp
    exact ⟨.some x y ((frob_nonsingular_iff p W x y).mp h), rfl⟩

theorem frobPt_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] : frobPt p W ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W 0
  intro h0
  have : frobPt p W (.some 0 y hy) = 0 := by rw [h0]; rfl
  rw [frobPt_some] at this
  exact Affine.Point.some_ne_zero _ this

theorem frobPt_mem_rationalHomSet (W : WeierstrassCurve k) :
    (frobPt p W : (W.baseChange k).toAffine.Point →+ ((frobTwist p W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (frobTwist p W) := by
  refine Or.inr ⟨C (X ^ p), 1, X ^ p, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : k[X][X]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C (X ^ p) : k[X][X]) x y = x ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (X ^ p : k[X][X]) x y = y ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  simp only [e0, e1, e2, div_one]
  exact ⟨frob_nonsingular p W h, rfl⟩

theorem hasHeight_frobPt (W : WeierstrassCurve k) [W.IsElliptic] : HasHeight p (frobPt p W) 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨X ^ p, 1, ∅, X, 1, ⟨isCoprime_one_right, ?_, Set.finite_empty, ?_⟩, ?_, ?_,
    isCoprime_one_right, by simp, ?_⟩
  · rw [natDegree_X_pow]; exact lt_of_lt_of_le hp (le_max_left _ _)
  · intro x y h _
    exact ⟨x ^ p, y ^ p, frob_nonsingular p W h, rfl, by simp⟩
  · rw [pow_one, expand_X]
  · rw [map_one]
  · simp [wronskian]

variable {W W₃ : WeierstrassCurve k} [W.IsElliptic] [W₃.IsElliptic]

theorem exists_eq_comp_frobPt_of_hasHeight {δ : W.toAffine.Point →+ W₃.toAffine.Point}
    (hδ : δ ∈ rationalHomSet k W W₃) (hδ0 : δ ≠ 0) {e : ℕ} (he : HasHeight p δ e) (h1 : 1 ≤ e) :
    ∃ γ ∈ rationalHomSet k (frobTwist p W) W₃, δ = γ.comp (frobPt p W) := by
  obtain ⟨u, v, B, c₁, c₂, hpair, hu, hv, hcc, -, -⟩ := he
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set d₁ := expand k (p ^ (e - 1)) c₁ with hd₁
  set d₂ := expand k (p ^ (e - 1)) c₂ with hd₂
  have hpe : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel h1]
  have hu' : u = expand k p d₁ := by rw [hu, hd₁, expand_expand, ← hpe]
  have hv' : v = expand k p d₂ := by rw [hv, hd₂, expand_expand, ← hpe]
  have hd : IsCoprime d₁ d₂ := (isCoprime_expand (pow_ne_zero _ hp)).mpr hcc
  have hr : IsCoprime (X : k[X]) 1 := isCoprime_one_right
  have hrw : wronskian (X : k[X]) 1 ≠ 0 := by simp [wronskian]
  have hker : ∀ T : W.toAffine.Point, frobPt p W T = 0 → δ T = 0 := by
    intro T hT
    have : T = 0 := frobPt_injective p W (by rw [hT, map_zero])
    rw [this, map_zero]
  have hρx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : (frobTwist p W).toAffine.Nonsingular x' y'),
        frobPt p W (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * (1 : k[X]).eval (x ^ p ^ 1) = (X : k[X]).eval (x ^ p ^ 1) := by
    intro x y h _
    exact ⟨x ^ p, y ^ p, frob_nonsingular p W h, rfl, by simp⟩
  have hδx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₃.toAffine.Nonsingular x' y'),
        δ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * d₂.eval (x ^ p ^ 1) = d₁.eval (x ^ p ^ 1) := by
    intro x y h hx
    obtain ⟨x', y', h', e1, r1⟩ := hpair.2.2.2 x y h hx
    refine ⟨x', y', h', e1, ?_⟩
    rw [pow_one, ← expand_eval, ← expand_eval, ← hu', ← hv']; exact r1
  exact WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W (frobTwist p W) W₃
    (frobPt_mem_rationalHomSet p W) hδ (frobPt_ne_zero p W) hδ0 hker 1 hr hrw hd hpair.2.2.1 hρx hδx

theorem exists_hasHeight_pos_comp_frobPt {γ : (frobTwist p W).toAffine.Point →+ W₃.toAffine.Point}
    (hγ : γ ∈ rationalHomSet k (frobTwist p W) W₃) (hγ0 : γ ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ HasHeight p (⇑γ ∘ ⇑(frobPt p W)) m := by
  obtain ⟨e, he⟩ := exists_hasHeight p hγ hγ0
  exact ⟨e + 1, Nat.le_add_left 1 e, he.comp p (hasHeight_frobPt p W)⟩

end Frobenius

section Quat

open QuaternionAlgebra
open scoped Quaternion

variable {a b : ℚ}

theorem quat_sq_sub_trd_mul_add_nrd (x : ℍ[ℚ, a, b]) :
    x * x - ((trd x : ℚ) : ℍ[ℚ, a, b]) * x + ((nrd x : ℚ) : ℍ[ℚ, a, b]) = 0 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  change _ - (⟨trd _, 0, 0, 0⟩ : ℍ[ℚ, a, b]) * _ + (⟨nrd _, 0, 0, 0⟩ : ℍ[ℚ, a, b]) = 0
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_sub_mk, QuaternionAlgebra.mk_add_mk,
    nrd_mk, trd_mk]
  ext <;> simp <;> ring

theorem quat_nrd_sub_intCast (x : ℍ[ℚ, a, b]) (m : ℤ) :
    nrd (x - (m : ℍ[ℚ, a, b])) = (m : ℚ) ^ 2 - trd x * m + nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [nrd, trd]
  ring

theorem quat_nrd_intCast (m : ℤ) : nrd ((m : ℍ[ℚ, a, b])) = (m : ℚ) ^ 2 := by
  simp [nrd]

theorem quat_nrd_pos_of_ne_zero (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : 0 < nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd_mk]
  have h1 : 0 ≤ x₀ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -a * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -b * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ a * b * x₃ ^ 2 := mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg ha hb)) (sq_nonneg _)
  by_contra hle
  push Not at hle
  have e0 : x₀ ^ 2 = 0 := by nlinarith
  have e1 : -a * x₁ ^ 2 = 0 := by nlinarith
  have e2 : -b * x₂ ^ 2 = 0 := by nlinarith
  have e3 : a * b * x₃ ^ 2 = 0 := by nlinarith
  have hx₀ : x₀ = 0 := by simpa using e0
  have hx₁ : x₁ = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · linarith
    · simpa using h
  have hx₂ : x₂ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · simpa using h
  have hx₃ : x₃ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · nlinarith [mul_pos_of_neg_of_neg ha hb]
    · simpa using h
  apply hx
  ext <;> assumption

theorem quat_intCast_eq_coe (m : ℤ) : ((m : ℤ) : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) := by
  ext <;> simp

end Quat

section Generic

variable {G : Type*} [AddCommGroup G]

theorem AddMonoidHom.comp_self_add_smul_id_eq_smul_of_forall (β : G →+ G) (t n : ℤ)
    (h : ∀ P, β (β P) - t • β P + n • P = 0) : β.comp β + n • AddMonoidHom.id G = t • β := by
  ext P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply]
  rw [← sub_eq_zero, ← h P]
  abel

theorem AddMonoidHom.apply_apply_eq_of_comp_self_add_smul_id_eq_smul (β : G →+ G) (t n : ℤ)
    (h : β.comp β + n • AddMonoidHom.id G = t • β) (P : G) : β (β P) = t • β P - n • P := by
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply] at this
  rw [← this, add_sub_cancel_right]

theorem AddMonoidHom.comp_self_sq_char (β : G →+ G) (t n : ℤ)
    (h : ∀ P, β (β P) = t • β P - n • P) :
    (β.comp β).comp (β.comp β) + (n ^ 2) • AddMonoidHom.id G = (t ^ 2 - 2 * n) • (β.comp β) := by
  ext P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply]
  rw [h (β P), map_sub, map_zsmul, map_zsmul, h (β P), h P]
  module

end Generic

section Frame

open QuaternionAlgebra
open scoped Quaternion

variable (X₀ : WeierstrassCurve k) [X₀.IsElliptic]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
  (θ : ↥(rationalEndSubring k X₀) →+* ℍ[ℚ, a, b])

theorem exists_int_nrd_trd (hΛ : IsOrder Λ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (r : rationalEndSubring k X₀) :
    ∃ n t : ℤ, (n : ℚ) = nrd (θ r) ∧ (t : ℚ) = trd (θ r) := by
  have hmem : θ r ∈ Λ := by
    have : θ r ∈ Set.range θ := ⟨r, rfl⟩
    rw [hθΛ] at this
    exact this
  obtain ⟨⟨n, hn⟩, ⟨t, ht⟩⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hmem
  exact ⟨n, t, hn, ht⟩

theorem sq_sub_mul_add_eq_zero (hθ : Function.Injective θ) (r : rationalEndSubring k X₀) {n t : ℤ}
    (hn : (n : ℚ) = nrd (θ r)) (ht : (t : ℚ) = trd (θ r)) :
    r * r - (t : rationalEndSubring k X₀) * r + (n : rationalEndSubring k X₀) = 0 := by
  apply hθ
  simp only [map_add, map_sub, map_mul, map_intCast, map_zero, quat_intCast_eq_coe]
  rw [ht, hn]
  exact quat_sq_sub_trd_mul_add_nrd (θ r)

theorem apply_apply_sub_add_eq_zero (hθ : Function.Injective θ) (r : rationalEndSubring k X₀) {n t : ℤ}
    (hn : (n : ℚ) = nrd (θ r)) (ht : (t : ℚ) = trd (θ r)) (P : (X₀.baseChange k).toAffine.Point) :
    (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) ((r : AddMonoid.End (X₀.baseChange k).toAffine.Point) P)
      - t • (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) P + n • P = 0 := by
  have h := sq_sub_mul_add_eq_zero X₀ θ hθ r hn ht
  have h1 : ((r : AddMonoid.End (X₀.baseChange k).toAffine.Point) * r
      - (t : AddMonoid.End (X₀.baseChange k).toAffine.Point) * r
      + (n : AddMonoid.End (X₀.baseChange k).toAffine.Point)) = 0 := by
    have := congr_arg Subtype.val h
    push_cast at this
    exact this
  have h2 := DFunLike.congr_fun h1 P
  simp at h2
  exact h2

theorem sub_apply_apply_eq_smul (hθ : Function.Injective θ) (r : rationalEndSubring k X₀) {n t : ℤ}
    (hn : (n : ℚ) = nrd (θ r)) (ht : (t : ℚ) = trd (θ r)) (P : (X₀.baseChange k).toAffine.Point) :
    (((t : rationalEndSubring k X₀) - r : rationalEndSubring k X₀) :
        AddMonoid.End (X₀.baseChange k).toAffine.Point)
      ((r : AddMonoid.End (X₀.baseChange k).toAffine.Point) P) = n • P := by
  have h := sq_sub_mul_add_eq_zero X₀ θ hθ r hn ht
  have hrbar_r : ((t : rationalEndSubring k X₀) - r) * r = (n : rationalEndSubring k X₀) := by
    rw [sub_mul, ← sub_eq_zero, ← neg_eq_zero, ← h]
    noncomm_ring
  have h1 : ((((t : rationalEndSubring k X₀) - r : rationalEndSubring k X₀) :
      AddMonoid.End (X₀.baseChange k).toAffine.Point) * r) =
        (n : AddMonoid.End (X₀.baseChange k).toAffine.Point) := by
    have := congr_arg Subtype.val hrbar_r
    push_cast at this ⊢
    exact this
  have h2 := DFunLike.congr_fun h1 P
  simpa [AddMonoid.End.coe_mul] using h2

end Frame

section Core

open QuaternionAlgebra
open scoped Quaternion

variable (p : ℕ) [Fact p.Prime] [CharP k p] (X₀ : WeierstrassCurve k) [X₀.IsElliptic]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
  (θ : ↥(rationalEndSubring k X₀) →+* ℍ[ℚ, a, b])

theorem dvd_nrd_of_eq_comp_frobPt (ha : a < 0) (hb : b < 0) (hΛ : IsOrder Λ)
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (r : rationalEndSubring k X₀)
    {ρ : ((frobTwist p X₀).baseChange k).toAffine.Point →+ (X₀.baseChange k).toAffine.Point}
    (hρ : ρ ∈ rationalHomSet k (frobTwist p X₀) X₀)
    (hr : (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) = ρ.comp (frobPt p X₀))
    (hr0 : (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) ≠ 0)
    {n : ℤ} (hn : (n : ℚ) = nrd (θ r)) : (p : ℤ) ∣ n := by
  obtain ⟨n', t, hn', ht⟩ := exists_int_nrd_trd X₀ Λ θ hΛ hθΛ r
  obtain rfl : n' = n := by exact_mod_cast hn'.trans hn.symm

  have hθr0 : θ r ≠ 0 := by
    intro h0
    apply hr0
    have : r = 0 := hθ (by rw [h0, map_zero])
    rw [this]; rfl
  have hnpos : (0 : ℤ) < n' := by
    have := quat_nrd_pos_of_ne_zero ha hb hθr0
    rw [← hn'] at this
    exact_mod_cast this
  by_contra hpn

  set rbar : rationalEndSubring k X₀ := (t : rationalEndSubring k X₀) - r with hrbar
  have hrP : ∀ P : (X₀.baseChange k).toAffine.Point,
      (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) P = ρ (frobPt p X₀ P) := by
    intro P
    have := DFunLike.congr_fun hr P
    exact this
  have hpt : ∀ P : (X₀.baseChange k).toAffine.Point,
      (rbar : AddMonoid.End (X₀.baseChange k).toAffine.Point) (ρ (frobPt p X₀ P)) = n' • P := by
    intro P
    rw [← hrP]
    exact sub_apply_apply_eq_smul X₀ θ hθ r hn' ht P

  have hrbar_mem : (rbar : AddMonoid.End (X₀.baseChange k).toAffine.Point) ∈ rationalHomSet k X₀ X₀ :=
    mem_rationalHomSet_of_mem_rationalEndSubring X₀ rbar.2
  set β : ((frobTwist p X₀).baseChange k).toAffine.Point →+ (X₀.baseChange k).toAffine.Point :=
    AddMonoidHom.comp (rbar : AddMonoid.End (X₀.baseChange k).toAffine.Point) ρ with hβ_def
  have hβmem : β ∈ rationalHomSet k (frobTwist p X₀) X₀ :=
    WeierstrassCurve.comp_mem_rationalHomSet k (frobTwist p X₀) X₀ X₀ hρ hrbar_mem
  have hβπ : ∀ P : (X₀.baseChange k).toAffine.Point, β (frobPt p X₀ P) = n' • P := fun P => hpt P
  set N : ℕ := n'.toNat with hN_def
  have hNn : (N : ℤ) = n' := Int.toNat_of_nonneg hnpos.le
  have hNk : (N : k) ≠ 0 := by
    intro h0
    have : p ∣ N := (CharP.cast_eq_zero_iff k p N).mp h0
    apply hpn
    rw [← hNn]; exact_mod_cast this
  have hker : ∀ Q : ((frobTwist p X₀).baseChange k).toAffine.Point, (N : ℤ) • Q = 0 → β Q = 0 := by
    intro Q hQ
    obtain ⟨P, hP⟩ := frobPt_surjective p X₀ Q
    have hP0 : (N : ℤ) • (P : (X₀.baseChange k).toAffine.Point) = 0 := by
      apply frobPt_injective p X₀
      rw [map_zsmul, map_zero]
      rw [← hP] at hQ
      exact hQ
    rw [← hP]
    change β (frobPt p X₀ P) = 0
    rw [hβπ, ← hNn]
    exact hP0
  obtain ⟨β', hβ'mem, hβ'⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero k (frobTwist p X₀) X₀ hNk hβmem hker

  set ε : (X₀.baseChange k).toAffine.Point →+ (X₀.baseChange k).toAffine.Point :=
    β'.comp (frobPt p X₀) - AddMonoidHom.id _ with hε_def
  have hεmem : ε ∈ rationalHomSet k X₀ X₀ :=
    sub_mem_rationalHomSet
      (WeierstrassCurve.comp_mem_rationalHomSet k X₀ (frobTwist p X₀) X₀ (frobPt_mem_rationalHomSet p X₀) hβ'mem)
      (id_mem_rationalHomSet k X₀)
  have hεapply : ∀ P : (X₀.baseChange k).toAffine.Point, ε P = β' (frobPt p X₀ P) - P := fun P => rfl
  have hεtor : ∀ P : (X₀.baseChange k).toAffine.Point, (N : ℤ) • ε P = 0 := by
    intro P
    have h1 : β (frobPt p X₀ P) = (N : ℤ) • β' (frobPt p X₀ P) := hβ' _
    rw [hβπ, ← hNn] at h1
    rw [hεapply, smul_sub, ← h1, sub_self]
  have hε0 : ε = 0 := by
    by_contra hne
    have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hεmem hne
    obtain ⟨P₀, hP₀⟩ := exists_zsmul_ne_zero X₀ (n := (N : ℤ)) (by rw [hNn]; exact hnpos.ne')
    obtain ⟨Q, hQ⟩ := hsurj P₀
    exact hP₀ (by rw [← hQ]; exact hεtor Q)

  have hεP : ∀ P : (X₀.baseChange k).toAffine.Point, β' (frobPt p X₀ P) - P = 0 := by
    intro P
    rw [← hεapply]
    exact DFunLike.congr_fun hε0 P
  have hfun : (fun P : (X₀.baseChange k).toAffine.Point => β' (frobPt p X₀ P)) = id :=
    funext fun P => sub_eq_zero.mp (hεP P)
  have hβ'0 : β' ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_nonsingular X₀ 0
    have h1 := hεP (.some 0 y hy)
    rw [h0, AddMonoidHom.zero_apply, zero_sub, neg_eq_zero] at h1
    exact Affine.Point.some_ne_zero _ h1
  have H0 : HasHeight p (W₁ := X₀) (W₂ := X₀)
      (fun P : (X₀.baseChange k).toAffine.Point => β' (frobPt p X₀ P)) 0 := by
    rw [hfun]
    exact hasHeight_id p (W₁ := X₀)
  obtain ⟨m, hm1, Hm⟩ := exists_hasHeight_pos_comp_frobPt p (W := X₀) (W₃ := X₀) hβ'mem hβ'0
  have := hasHeight_unique p Hm H0
  omega

theorem exists_mulP_eq_comp_frobPt :
    ∃ V ∈ rationalHomSet k (frobTwist p X₀) X₀,
      ((p : ℤ) • AddMonoidHom.id X₀.toAffine.Point) = V.comp (frobPt p X₀) := by
  obtain ⟨π₀, hπ₀, H⟩ := exists_hasHeight_mulP X₀ p
  have hmem : ((p : ℤ) • AddMonoidHom.id X₀.toAffine.Point) ∈ rationalHomSet k X₀ X₀ :=
    zsmul_mem_rationalHomSet (id_mem_rationalHomSet k X₀) _
  have hne : ((p : ℤ) • AddMonoidHom.id X₀.toAffine.Point) ≠ 0 := by
    obtain ⟨P, hP⟩ := exists_zsmul_ne_zero X₀ (n := (p : ℤ)) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    intro h0
    apply hP
    have := DFunLike.congr_fun h0 P
    simpa using this
  have H' : HasHeight p ((p : ℤ) • AddMonoidHom.id X₀.toAffine.Point) π₀ := by
    have e : (⇑((p : ℤ) • AddMonoidHom.id X₀.toAffine.Point) : X₀.toAffine.Point → X₀.toAffine.Point) =
        fun P => (p : ℤ) • P := by
      funext P; simp
    unfold HasHeight; rw [e]; exact H
  exact exists_eq_comp_frobPt_of_hasHeight p hmem hne H' hπ₀

theorem exists_eq_comp_frobPt_of_dvd_nrd (ha : a < 0) (hb : b < 0) (hΛ : IsOrder Λ)
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hss : ∀ P : X₀.toAffine.Point, p • P = 0 → P = 0)
    (r : rationalEndSubring k X₀)
    (hr0 : (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) ≠ 0)
    {n : ℤ} (hn : (n : ℚ) = nrd (θ r)) (hpn : (p : ℤ) ∣ n) :
    ∃ γ ∈ rationalHomSet k (frobTwist p X₀) X₀,
      (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) = γ.comp (frobPt p X₀) := by
  obtain ⟨n', t, hn', ht⟩ := exists_int_nrd_trd X₀ Λ θ hΛ hθΛ r
  obtain rfl : n' = n := by exact_mod_cast hn'.trans hn.symm
  obtain ⟨V, hVmem, hV⟩ := exists_mulP_eq_comp_frobPt p X₀
  have hVP : ∀ P : (X₀.baseChange k).toAffine.Point, V (frobPt p X₀ P) = (p : ℤ) • P := by
    intro P
    have := DFunLike.congr_fun hV P
    have h__af := this.symm
    simp at h__af
    exact h__af
  set β : X₀.toAffine.Point →+ X₀.toAffine.Point :=
    (r : AddMonoid.End (X₀.baseChange k).toAffine.Point) with hβ_def
  have hβmem : β ∈ rationalHomSet k X₀ X₀ := mem_rationalHomSet_of_mem_rationalEndSubring X₀ r.2
  have hβ0 : β ≠ 0 := hr0
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out

  by_cases hscalar : ∃ m : ℤ, θ r = (m : ℍ[ℚ, a, b])
  · obtain ⟨m, hm⟩ := hscalar
    have hrm : r = (m : rationalEndSubring k X₀) := hθ (by rw [hm, map_intCast])
    have hnm : n' = m ^ 2 := by
      have : (n' : ℚ) = (m : ℚ) ^ 2 := by rw [hn', hm, quat_nrd_intCast]
      exact_mod_cast this
    have hpm : (p : ℤ) ∣ m := hpp.dvd_of_dvd_pow (by rw [← hnm]; exact hpn)
    obtain ⟨c, hc⟩ := hpm
    refine ⟨c • V, zsmul_mem_rationalHomSet hVmem c, ?_⟩
    apply AddMonoidHom.ext
    intro P
    have h1 : β P = m • P := by
      rw [hβ_def, hrm]
      change ((m : rationalEndSubring k X₀) : AddMonoid.End (X₀.baseChange k).toAffine.Point) P = m • P
      rw [Subring.coe_intCast, AddMonoid.End.intCast_apply]
      rfl
    change β P = (c • V) (frobPt p X₀ P)
    rw [h1, AddMonoidHom.zsmul_apply, hVP, smul_smul, mul_comm, ← hc]
    rfl

  have hirr : ∀ m : ℤ, m ^ 2 - t * m + n' ≠ 0 := by
    intro m hm0
    apply hscalar
    refine ⟨m, ?_⟩
    have h1 : nrd (θ r - (m : ℍ[ℚ, a, b])) = 0 := by
      rw [quat_nrd_sub_intCast, ← hn', ← ht]
      exact_mod_cast hm0
    by_contra hne
    have := quat_nrd_pos_of_ne_zero ha hb (sub_ne_zero.mpr hne)
    rw [h1] at this
    exact lt_irrefl _ this
  have hchar : β.comp β + n' • AddMonoidHom.id _ = t • β :=
    AddMonoidHom.comp_self_add_smul_id_eq_smul_of_forall β t n'
      (fun P => apply_apply_sub_add_eq_zero X₀ θ hθ r hn' ht P)

  have hpt : (p : ℤ) ∣ t := by
    by_contra hnt
    obtain ⟨T, hT0, hT⟩ :=
      WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
        p X₀ hβmem t n' hchar hirr hpn hnt
    exact hT0 (hss T hT)
  have hββ : ∀ P, β (β P) = t • β P - n' • P :=
    AddMonoidHom.apply_apply_eq_of_comp_self_add_smul_id_eq_smul β t n' hchar

  set β₂ : X₀.toAffine.Point →+ X₀.toAffine.Point := β.comp β with hβ₂_def
  have hβ₂mem : β₂ ∈ rationalHomSet k X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet k X₀ X₀ X₀ hβmem hβmem
  have hchar₂ : β₂.comp β₂ + (n' ^ 2) • AddMonoidHom.id _ = (t ^ 2 - 2 * n') • β₂ :=
    AddMonoidHom.comp_self_sq_char β t n' hββ
  obtain ⟨γ₂, hγ₂mem, hγ₂⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd p X₀ hβ₂mem
      (t ^ 2 - 2 * n') (n' ^ 2) hchar₂ 0 (by
        have : (t ^ 2 - 2 * n') - 2 * 0 = t * t - 2 * n' := by ring
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_left hpt t) (dvd_mul_of_dvd_right hpn 2))
      (by
        have : (0 : ℤ) ^ 2 - (t ^ 2 - 2 * n') * 0 + n' ^ 2 = n' ^ 2 := by ring
        rw [this]
        exact pow_dvd_pow_of_dvd hpn 2)

  set g : ((frobTwist p X₀).baseChange k).toAffine.Point →+ (X₀.baseChange k).toAffine.Point :=
    γ₂.comp V with hg_def
  have hgmem : g ∈ rationalHomSet k (frobTwist p X₀) X₀ :=
    WeierstrassCurve.comp_mem_rationalHomSet k (frobTwist p X₀) X₀ X₀ hVmem hγ₂mem
  have hβ₂g : (⇑β₂ : X₀.toAffine.Point → X₀.toAffine.Point) = ⇑g ∘ ⇑(frobPt p X₀) := by
    funext P
    have h1 : β₂ P = (p : ℤ) • γ₂ P := by
      have := DFunLike.congr_fun hγ₂ P
      change β₂ P - (0 : ℤ) • P = (p : ℤ) • γ₂ P at this
      rwa [zero_zsmul, sub_zero] at this
    rw [h1, Function.comp_apply]
    change _ = γ₂ (V (frobPt p X₀ P))
    rw [hVP, map_zsmul]
  have hβsurj : Function.Surjective β := WeierstrassCurve.surjective_of_mem_rationalHomSet k hβmem hβ0
  have hβ₂0 : β₂ ≠ 0 := by
    intro h0
    apply hβ0
    apply AddMonoidHom.ext
    intro Q
    obtain ⟨P, rfl⟩ := hβsurj Q
    have := DFunLike.congr_fun h0 P
    exact this
  have hg0 : g ≠ 0 := by
    intro h0
    apply hβ₂0
    apply AddMonoidHom.ext
    intro P
    have := congr_fun hβ₂g P
    rw [h0] at this
    exact this

  obtain ⟨m, hm1, Hm'⟩ := exists_hasHeight_pos_comp_frobPt p (W := X₀) (W₃ := X₀) hgmem hg0
  have Hm : HasHeight p (W₁ := X₀) (W₂ := X₀) (⇑β₂) m := by
    rw [hβ₂g]
    exact Hm'
  obtain ⟨e, He⟩ := exists_hasHeight p hβmem hβ0
  have He2 : HasHeight p (⇑β₂) (e + e) := He.comp p He
  have hme : e + e = m := hasHeight_unique p He2 Hm
  have he1 : 1 ≤ e := by omega
  exact exists_eq_comp_frobPt_of_hasHeight p hβmem hβ0 He he1

end Core

section Assembly

open QuaternionAlgebra
open scoped Quaternion

theorem frobPt_eq_ratPointHom {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (W : WeierstrassCurve κ) :
    frobPt p W = WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W) := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem main {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    θ '' (WeierstrassCurve.kernelIdealSet κ X₀ (frobTwist q' X₀) (frobPt q' X₀)) =
      {h | h ∈ Λ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))} := by
  have ha : a < 0 := hdef.neg_left
  have hb : b < 0 := hdef.neg_right
  have hO : IsOrder Λ := hΛ.isOrder
  ext h
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, ⟨ρ, hρ, hrρ⟩, rfl⟩
    have hmem : θ r ∈ Λ := by
      have : θ r ∈ Set.range θ := ⟨r, rfl⟩
      rw [hθΛ] at this
      exact this
    refine ⟨hmem, ?_⟩
    by_cases hr0 : (r : AddMonoid.End (X₀.baseChange κ).toAffine.Point) = 0
    · left
      have : r = 0 := Subtype.ext hr0
      rw [this, map_zero]
    · right
      obtain ⟨n, t, hn, -⟩ := exists_int_nrd_trd X₀ Λ θ hO hθΛ r
      have hdvd := dvd_nrd_of_eq_comp_frobPt q' X₀ Λ θ ha hb hO hθ hθΛ r hρ hrρ hr0 hn
      rw [← hn, padicValRat.of_int]
      have hn0 : n ≠ 0 := by
        intro h0
        have hθr0 : θ r ≠ 0 := by
          intro e0; apply hr0
          have : r = 0 := hθ (by rw [e0, map_zero])
          rw [this]; rfl
        have := quat_nrd_pos_of_ne_zero ha hb hθr0
        rw [← hn, h0] at this
        exact lt_irrefl _ (by exact_mod_cast this)
      rcases (padicValInt_dvd_iff 1 n).mp (by rw [pow_one]; exact hdvd) with h0 | h1
      · exact absurd h0 hn0
      · exact_mod_cast h1
  · rintro ⟨hΛh, hcase⟩
    have hrange : h ∈ Set.range θ := by rw [hθΛ]; exact hΛh
    obtain ⟨r, rfl⟩ := hrange
    rcases hcase with h0 | h1
    · refine ⟨0, WeierstrassCurve.zero_mem_kernelIdealSet κ X₀ _ _, ?_⟩
      rw [map_zero, h0]
    · obtain ⟨n, t, hn, -⟩ := exists_int_nrd_trd X₀ Λ θ hO hθΛ r
      rw [← hn, padicValRat.of_int] at h1
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at h1
      have hr0 : (r : AddMonoid.End (X₀.baseChange κ).toAffine.Point) ≠ 0 := by
        intro e0
        have hr : r = 0 := Subtype.ext e0
        apply hn0
        have : (n : ℚ) = 0 := by rw [hn, hr, map_zero, nrd_zero]
        exact_mod_cast this
      have hdvd : (q' : ℤ) ∣ n := by
        have := (padicValInt_dvd_iff 1 n).mpr (Or.inr (by exact_mod_cast h1))
        rwa [pow_one] at this
      obtain ⟨γ, hγ, hrγ⟩ := exists_eq_comp_frobPt_of_dvd_nrd q' X₀ Λ θ ha hb hO hθ hθΛ hss r hr0 hn hdvd
      exact ⟨r, ⟨γ, hγ, hrγ⟩, rfl⟩

end Assembly

end FrobeniusKernelIdealPinned
p2m_reactivate "P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd.FrobeniusKernelIdealPinned"

open scoped Quaternion
open QuaternionAlgebra

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    θ '' WeierstrassCurve.kernelIdealSet κ X₀ (X₀.map (frobenius κ q'))
        (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := X₀)) =
      {h | h ∈ Λ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))} := by
  rw [← FrobeniusKernelIdealPinned.frobPt_eq_ratPointHom]
  exact FrobeniusKernelIdealPinned.main q' X₀ hss a b hdef Λ hΛ θ hθ hθΛ

end S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd
end P2MW
export P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd (solution)
