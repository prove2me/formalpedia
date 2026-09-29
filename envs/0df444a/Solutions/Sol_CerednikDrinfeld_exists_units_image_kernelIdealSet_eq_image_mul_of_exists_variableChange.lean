-- Prove2me | solution 1 for CerednikDrinfeld.exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fbeeda9d-3765-593e-be87-5447ba50a136

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open scoped Quaternion Polynomial.Bivariate
open QuaternionAlgebra WeierstrassCurve

namespace CerednikDrinfeld
namespace K2aOfVariableChange

section Definite

variable {a b : ℚ}

theorem nrd_pos_of_ne_zero (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : 0 < nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd_mk]
  have h1 : 0 ≤ x₀ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -a * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -b * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ a * b * x₃ ^ 2 := mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg ha hb)) (sq_nonneg _)
  by_contra hle
  push Not at hle
  have e1 : x₀ ^ 2 = 0 := by nlinarith
  have e2 : -a * x₁ ^ 2 = 0 := by nlinarith
  have e3 : -b * x₂ ^ 2 = 0 := by nlinarith
  have e4 : a * b * x₃ ^ 2 = 0 := by nlinarith
  have hx₀ : x₀ = 0 := by simpa using e1
  have hx₁ : x₁ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · simpa using h
  have hx₂ : x₂ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · linarith
    · simpa using h
  have hx₃ : x₃ = 0 := by
    rcases mul_eq_zero.mp e4 with h | h
    · exact absurd h (mul_pos_of_neg_of_neg ha hb).ne'
    · simpa using h
  exact hx (by subst hx₀ hx₁ hx₂ hx₃; rfl)

theorem isUnit_of_ne_zero (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : IsUnit x := by
  have hn : nrd x ≠ 0 := (nrd_pos_of_ne_zero ha hb hx).ne'
  refine ⟨⟨x, (nrd x)⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, mul_star_eq_coe_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn,
      QuaternionAlgebra.coe_one]
  · rw [smul_mul_assoc, star_mul_eq_coe_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn,
      QuaternionAlgebra.coe_one]

end Definite

section VarChange

p2m_open "Polynomial Polynomial.Bivariate.Polynomial"

variable {k : Type*} [Field k] [DecidableEq k]

omit [DecidableEq k] in
private theorem exists_eq_some {W : WeierstrassCurve k}
    {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀)
    (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem addEquiv_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.toAddMonoidHom : (W.baseChange k).toAffine.Point →+ ((γ • W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (γ • W) := by
  right
  refine ⟨C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)), 1,
    C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 2 * (x - γ.r) := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t)) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  obtain ⟨h', hP⟩ := he x y h
  exact exists_eq_some hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem addEquiv_symm_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.symm.toAddMonoidHom :
        ((γ • W).baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k (γ • W) W := by
  right
  refine ⟨C (C ((γ.u : k) ^ 2) * X + C γ.r), 1,
    C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t), 1, ∅,
    Set.finite_empty, fun x' y' h' _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x' y' = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((γ.u : k) ^ 2) * X + C γ.r) : k[X][Y]) x' y' =
      (γ.u : k) ^ 2 * x' + γ.r := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t) : k[X][Y]) x' y' =
      (γ.u : k) ^ 3 * y' + ((γ.u : k) ^ 2 * γ.s * x' + γ.t) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  set P := e.symm (.some x' y' h') with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    have : e P = e 0 := by rw [h0]
    rw [hPdef, AddEquiv.apply_symm_apply, _root_.map_zero] at this
    exact Affine.Point.some_ne_zero _ this
  rcases hPxy : P with _ | ⟨x, y, h⟩
  · exact absurd hPxy hP0
  · obtain ⟨h'', hexy⟩ := he x y h
    have key : e (.some x y h) = .some x' y' h' := by
      rw [← hPxy, hPdef, AddEquiv.apply_symm_apply]
    rw [hexy] at key
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj key
    have hw : (↑γ.u⁻¹ : k) = (γ.u : k)⁻¹ := Units.val_inv_eq_inv_val γ.u
    have hu0 : (γ.u : k) ≠ 0 := γ.u.ne_zero
    have hPe : e.symm.toAddMonoidHom (.some x' y' h') = .some x y h := by
      show e.symm (.some x' y' h') = .some x y h
      rw [← hPdef]; exact hPxy
    refine exists_eq_some hPe ?_ ?_
    · rw [e0, e1, div_one, ← hx, hw]
      field_simp
      ring
    · rw [e0, e2, div_one, ← hx, ← hy, hw]
      field_simp
      ring

end VarChange

section Torsion

variable {κ : Type*} [Field κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem infinite_point [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] :
    Infinite (W.baseChange κ).toAffine.Point := by
  haveI : (W.baseChange κ).IsElliptic := (inferInstance : (W.map (algebraMap κ κ)).IsElliptic)
  have hy : ∀ x : κ, ∃ y : κ, (W.baseChange κ).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange κ).toAffine.polynomial.map (Polynomial.evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange κ).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : κ => (Affine.Point.some x (f x) (hf x) : (W.baseChange κ).toAffine.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem exists_zsmul_ne_zero [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∀ P : (W.baseChange κ).toAffine.Point, p • P = 0 → P = 0) {n : ℤ} (hn : 0 < n) :
    ∃ P : (W.baseChange κ).toAffine.Point, n • P ≠ 0 := by

  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn.le⟩
  subst hN
  have hN0 : N ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, m, hm, hNkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p (Fact.out : p.Prime).ne_one

  have hstrip : ∀ (j : ℕ) (P : (W.baseChange κ).toAffine.Point), (p ^ j) • P = 0 → P = 0 := by
    intro j
    induction j with
    | zero => intro P hP; simpa using hP
    | succ j ih =>
      intro P hP
      rw [pow_succ, mul_smul] at hP
      exact hW P (ih _ hP)
  by_contra hall
  push Not at hall
  have hm0 : m ≠ 0 := by rintro rfl; simp at hNkm; exact hN0 hNkm
  have hmκ : ((m : ℕ) : κ) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff κ p m).mp h)

  have htors : ∀ P : (W.baseChange κ).toAffine.Point, P ∈ Submodule.torsionBy ℤ _ (m : ℤ) := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    have h1 : (p ^ k) • (m • P) = 0 := by
      rw [← mul_smul, ← hNkm, ← natCast_zsmul]
      exact hall P
    have h2 := hstrip k _ h1
    rw [natCast_zsmul]
    exact h2
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W (n := m) hmκ
  haveI : Finite ↥(Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (m : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact pow_ne_zero 2 hm0
  haveI := infinite_point W
  haveI : Finite (W.baseChange κ).toAffine.Point :=
    Finite.of_injective (fun P => (⟨P, htors P⟩ : ↥(Submodule.torsionBy ℤ _ (m : ℤ))))
      (fun P Q h => congrArg Subtype.val h)
  exact not_finite (W.baseChange κ).toAffine.Point

end Torsion

section Main

theorem exists_units_image_kernelIdealSet_eq_image_mul_smul
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (ha : a < 0) (hb : b < 0)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (γ : VariableChange κ)
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : (X₀.baseChange κ).toAffine.Point →+ ((γ • W).baseChange κ).toAffine.Point)
    (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ (γ • W)) (hχ'0 : χ' ≠ 0) :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ (γ • W) χ') =
        (· * (c : ℍ[ℚ, a, b])) '' (θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ)) := by
  classical

  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange W γ
  have he₁ := addEquiv_mem_rationalHomSet W γ e he
  have he₂ := addEquiv_symm_mem_rationalHomSet W γ e he

  set χ₂ : (X₀.baseChange κ).toAffine.Point →+ ((γ • W).baseChange κ).toAffine.Point :=
    (e.toAddMonoidHom : (W.baseChange κ).toAffine.Point →+ ((γ • W).baseChange κ).toAffine.Point).comp χ
    with hχ₂def
  have hχ₂ : χ₂ ∈ rationalHomSet κ X₀ (γ • W) := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W (γ • W) hχ he₁
  have hχ₂0 : χ₂ ≠ 0 := by
    intro h0
    apply hχ0
    ext P
    have hP : e (χ P) = 0 := by
      show χ₂ P = 0
      rw [h0]; rfl
    have h2 := congrArg e.symm hP
    rw [AddEquiv.symm_apply_apply, map_zero] at h2
    rw [AddMonoidHom.zero_apply]
    exact h2

  obtain ⟨σ₂, hσ₂, n, hn, hdual⟩ :=
    WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ (γ • W) hχ₂ hχ₂0

  have hs : σ₂.comp χ' ∈ rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ (γ • W) X₀ hχ' hσ₂
  set s : ↥(rationalEndSubring κ X₀) := ⟨σ₂.comp χ', Subring.subset_closure hs⟩ with hsdef

  have hA : ∀ a' ∈ kernelIdealSet κ X₀ (γ • W) χ', ∃ b' ∈ kernelIdealSet κ X₀ W χ, a' * (n : ↥(rationalEndSubring κ X₀)) = b' * s := by
    rintro a' ⟨ρ, hρ, hρa⟩
    have hρe : ρ.comp (e.toAddMonoidHom : (W.baseChange κ).toAffine.Point →+ ((γ • W).baseChange κ).toAffine.Point)
        ∈ rationalHomSet κ W X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ W (γ • W) X₀ he₁ hρ
    have hb : (ρ.comp (e.toAddMonoidHom : (W.baseChange κ).toAffine.Point →+ ((γ • W).baseChange κ).toAffine.Point)).comp χ
        ∈ rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ hρe
    refine ⟨⟨_, Subring.subset_closure hb⟩, ⟨_, hρe, rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (a' : AddMonoid.End (X₀.baseChange κ).toAffine.Point) (((n : ↥(rationalEndSubring κ X₀)) :
        AddMonoid.End (X₀.baseChange κ).toAffine.Point) P) = ρ (e (χ (σ₂ (χ' P))))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρa]
    show ρ (χ' (n • P)) = ρ (e (χ (σ₂ (χ' P))))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    rfl
  have hB : ∀ b' ∈ kernelIdealSet κ X₀ W χ, ∃ a' ∈ kernelIdealSet κ X₀ (γ • W) χ', b' * s = a' * (n : ↥(rationalEndSubring κ X₀)) := by
    rintro b' ⟨ρ', hρ', hρb⟩
    have hρ : ρ'.comp (e.symm.toAddMonoidHom : ((γ • W).baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
        ∈ rationalHomSet κ (γ • W) X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ (γ • W) W X₀ he₂ hρ'
    have ha : (ρ'.comp (e.symm.toAddMonoidHom :
        ((γ • W).baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)).comp χ' ∈ rationalHomSet κ X₀ X₀ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ X₀ (γ • W) X₀ hχ' hρ
    refine ⟨⟨_, Subring.subset_closure ha⟩, ⟨_, hρ, rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (b' : AddMonoid.End (X₀.baseChange κ).toAffine.Point) (σ₂ (χ' P)) =
      ρ' (e.symm (χ' (((n : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P)))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρb]
    show ρ' (χ (σ₂ (χ' P))) = ρ' (e.symm (χ' (n • P)))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    show ρ' (χ (σ₂ (χ' P))) = ρ' (e.symm (e (χ (σ₂ (χ' P)))))
    rw [AddEquiv.symm_apply_apply]

  have hn0 : (n : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h
    have h2 := congrArg QuaternionAlgebra.re h
    rw [QuaternionAlgebra.re_intCast] at h2
    have h3 : (n : ℚ) = 0 := h2
    exact hn.ne' (by exact_mod_cast h3)
  obtain ⟨un, hun⟩ := isUnit_of_ne_zero ha hb hn0
  have hs0 : s ≠ 0 := by
    intro h0
    have hσ0 : σ₂ = 0 := by
      ext Q
      obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ' hχ'0 Q
      have := congrArg (fun t : ↥(rationalEndSubring κ X₀) => (t : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P) h0
      simp [hsdef] at this
      exact this
    obtain ⟨P, hP⟩ := exists_zsmul_ne_zero q' X₀ (fun P hP => hss P hP) hn
    exact hP (by rw [← hdual.comp_left P, hσ0]; rfl)
  have hθs0 : θ s ≠ 0 := fun h => hs0 (hθ (by rw [h, map_zero]))
  obtain ⟨us, hus⟩ := isUnit_of_ne_zero ha hb hθs0

  refine ⟨us * un⁻¹, ?_⟩
  ext y
  simp only [Set.mem_image, exists_exists_and_eq_and, Units.val_mul]
  constructor
  · rintro ⟨a', ha', rfl⟩
    obtain ⟨b', hb', hab⟩ := hA a' ha'
    refine ⟨b', hb', ?_⟩
    have h1 : θ a' * (n : ℍ[ℚ, a, b]) = θ b' * θ s := by
      rw [← map_intCast θ, ← map_mul, ← map_mul, hab]
    rw [hus, ← mul_assoc, ← h1, ← hun, Units.mul_inv_cancel_right]
  · rintro ⟨b', hb', rfl⟩
    obtain ⟨a', ha', hba⟩ := hB b' hb'
    refine ⟨a', ha', ?_⟩
    have h1 : θ b' * θ s = θ a' * (n : ℍ[ℚ, a, b]) := by
      rw [← map_intCast θ, ← map_mul, ← map_mul, hba]
    rw [hus, ← mul_assoc, h1, ← hun, Units.mul_inv_cancel_right]

theorem exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (ha : a < 0) (hb : b < 0)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : (X₀.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (hW : ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W') :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W' χ') =
        (· * (c : ℍ[ℚ, a, b])) '' (θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ)) := by
  obtain ⟨γ, rfl⟩ := hW
  exact exists_units_image_kernelIdealSet_eq_image_mul_smul q' X₀ hss a b ha hb θ hθ W γ χ hχ hχ0 χ' hχ' hχ'0

end Main

section JForm

theorem exists_units_image_kernelIdealSet_eq_image_mul_of_j_eq
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (ha : a < 0) (hb : b < 0)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : (X₀.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0) (hj : W.j = W'.j) :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W' χ') =
        (· * (c : ℍ[ℚ, a, b])) '' (θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ)) :=
  exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange q' X₀ hss a b ha hb θ hθ W W' χ hχ hχ0 χ' hχ'
    hχ'0 (WeierstrassCurve.exists_variableChange_of_j_eq W W' hj)

theorem j_eq_of_exists_variableChange {κ : Type} [Field κ] (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (hW : ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W') : W.j = W'.j := by
  obtain ⟨γ, rfl⟩ := hW
  exact (W.variableChange_j γ).symm

end JForm

end CerednikDrinfeld.K2aOfVariableChange

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (ha : a < 0) (hb : b < 0)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : (X₀.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (hW : ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W') :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W' χ') =
        (· * (c : ℍ[ℚ, a, b])) '' (θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ)) :=
  CerednikDrinfeld.K2aOfVariableChange.exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange q' X₀ hss
    a b ha hb θ hθ W W' χ hχ hχ0 χ' hχ' hχ'0 hW

end S_CerednikDrinfeld_exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
end P2MW
export P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange (solution)
