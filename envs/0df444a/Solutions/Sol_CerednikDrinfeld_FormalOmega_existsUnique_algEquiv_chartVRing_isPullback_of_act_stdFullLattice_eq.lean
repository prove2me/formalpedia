-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/beb3c4e4-a066-5837-8dd4-5246872120ca

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaE

section Coord

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) : 𝒪 := Classical.choose (w.2 i)

theorem algebraMap_coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordFun w i) = (w : Fin 2 → K) i := Classical.choose_spec (w.2 i)

def coordEquiv : ↥(stdLattice 𝒪 K) ≃ₗ[𝒪] (Fin 2 → 𝒪) where
  toFun := coordFun
  map_add' v w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, Pi.add_apply, map_add, algebraMap_coordFun, algebraMap_coordFun]
    rfl
  map_smul' r w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, algebraMap_coordFun,
      Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
  invFun a := ⟨fun i => algebraMap 𝒪 K (a i), fun i => ⟨a i, rfl⟩⟩
  left_inv w := Subtype.ext (funext fun i => algebraMap_coordFun w i)
  right_inv a := funext fun i => IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordFun])

theorem algebraMap_coordEquiv (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordEquiv w i) = (w : Fin 2 → K) i := algebraMap_coordFun w i

theorem coordEquiv_eq_of {w : ↥(stdLattice 𝒪 K)} {i : Fin 2} {r : 𝒪} (h : (w : Fin 2 → K) i = algebraMap 𝒪 K r) :
    coordEquiv w i = r :=
  IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordEquiv, h])

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

theorem stdBasis_repr (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (i : Fin 2) : stdBasis.repr w i = coordEquiv w i := by
  show (Module.Basis.ofEquivFun coordEquiv).repr w i = _
  rw [Module.Basis.ofEquivFun_repr_apply]

theorem stdBasis_apply (i : Fin 2) : stdBasis i = stdBasisVec (𝒪 := 𝒪) K i := by
  apply stdBasis.repr.injective
  ext j
  rw [Module.Basis.repr_self, stdBasis_repr, coordEquiv_stdBasisVec, Finsupp.single_apply, Pi.single_apply]
  simp only [eq_comm]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

theorem tensorBasis_apply (i : Fin 2) : tensorBasis B i = (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K i := by
  rw [tensorBasis, Algebra.TensorProduct.basis_apply, stdBasis_apply]

private def _root_.F2AlphaE.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "F2AlphaE" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

omit B in
theorem coordEquiv_smul_stdBasisVec (r : 𝒪) (j i : Fin 2) :
    coordEquiv (r • stdBasisVec (𝒪 := 𝒪) K j) i = r * (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show r • ((Pi.single j (1 : K) : Fin 2 → K) i) = algebraMap 𝒪 K (r * (Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, mul_one, Algebra.smul_def, mul_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero, mul_zero, map_zero]

theorem coord_tmul_smul_stdBasisVec (i j : Fin 2) (b : B) (r : 𝒪) :
    coord B i (b ⊗ₜ[𝒪] (r • stdBasisVec (𝒪 := 𝒪) K j)) = if i = j then b * algebraMap 𝒪 B r else 0 := by
  rw [coord_tmul, coordEquiv_smul_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem eq_sum_coord (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    x = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
  have h := (tensorBasis B).sum_repr x
  rw [Fin.sum_univ_two, tensorBasis_apply, tensorBasis_apply] at h
  exact h.symm

theorem inclBaseChange_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (b : B) (v : ↥M₁.1) :
    inclBaseChange B h (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) :=
  rfl

theorem eq_of_span_tmul_add_one_tmul_eq (a a' : B)
    (h : Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} =
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}) : a = a' := by
  have hmem : a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 ∈
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrArg (coord B 1) ht
  have h0 := congrArg (coord B 0) ht
  simp only [map_smul, map_add, coord_tmul_stdBasisVec, smul_eq_mul] at h0 h1
  simp at h0 h1
  rw [h1, one_mul] at h0
  exact h0.symm

end Coord

section Units

open Polynomial

theorem exists_mul_add_C_mul_of_map_dvd {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (p w : 𝒪[X])
    (h : p.map (Ideal.Quotient.mk (Ideal.span {π})) ∣ w.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    ∃ q s : 𝒪[X], w = p * q + C π * s := by
  obtain ⟨qbar, hq⟩ := h
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (Ideal.span {π})) Ideal.Quotient.mk_surjective qbar
  have hker : w - p * q ∈ RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span {π}))) := by
    rw [RingHom.mem_ker, Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hq, sub_self]
  rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hker
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hker
  exact ⟨q, s, by rw [← hs]; ring⟩

theorem isUnit_aeval_of_eq_mul_add {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {A : Type} [CommRing A] [Algebra 𝒪 A]
    (hA : IsNilpotent (algebraMap 𝒪 A π)) (ζ : A) (p q s w : 𝒪[X]) (h : w = p * q + C π * s)
    (hw : IsUnit (aeval ζ w)) : IsUnit (aeval ζ p) := by
  have e : aeval ζ p * aeval ζ q = aeval ζ w + -(algebraMap 𝒪 A π * aeval ζ s) := by
    rw [h, map_add, map_mul, map_mul, Polynomial.aeval_C]; ring
  have hn : IsNilpotent (-(algebraMap 𝒪 A π * aeval ζ s)) :=
    (Commute.isNilpotent_mul_right (Commute.all _ _) hA).neg
  obtain ⟨u, hu⟩ := hw
  have : IsUnit (aeval ζ p * aeval ζ q) := by
    rw [e, ← hu, show (u : A) + -(algebraMap 𝒪 A π * aeval ζ s) = u * (1 + ↑u⁻¹ * -(algebraMap 𝒪 A π * aeval ζ s)) by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]]
    exact (Units.isUnit u).mul (IsNilpotent.isUnit_one_add (Commute.isNilpotent_mul_left (Commute.all _ _) hn))
  exact isUnit_of_mul_isUnit_left this

theorem isUnit_of_not_mem_span {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (x : 𝒪) (hx : x ∉ Ideal.span {π}) : IsUnit x := by
  haveI := hdvr
  have hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  rw [IsLocalRing.eq_maximalIdeal hmax] at hx
  by_contra hu
  exact hx ((IsLocalRing.mem_maximalIdeal x).mpr hu)

theorem isUnit_linear {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    {A : Type} [CommRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π))
    (ζ : A) (hζ : IsUnit (ζ ^ r - ζ)) (c d : 𝒪) (hcd : c ∉ Ideal.span {π} ∨ d ∉ Ideal.span {π}) :
    IsUnit (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) := by
  by_cases hc : c ∈ Ideal.span {π}
  ·
    have hd : IsUnit d := isUnit_of_not_mem_span hdvr π hπ d (hcd.resolve_left (not_not.mpr hc))
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hc
    have hn : IsNilpotent (algebraMap 𝒪 A (c' * π) * ζ) := by
      rw [map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) (Commute.isNilpotent_mul_left (Commute.all _ _) hA)
    obtain ⟨u, hu⟩ := hd.map (algebraMap 𝒪 A)
    rw [← hu, show algebraMap 𝒪 A (c' * π) * ζ + ↑u = u * (1 + ↑u⁻¹ * (algebraMap 𝒪 A (c' * π) * ζ)) by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_comm]]
    exact (Units.isUnit u).mul (IsNilpotent.isUnit_one_add (Commute.isNilpotent_mul_left (Commute.all _ _) hn))
  ·
    haveI := hdvr
    haveI hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
    have hcu : IsUnit c := isUnit_of_not_mem_span hdvr π hπ c hc
    obtain ⟨ci, hci⟩ : ∃ ci : 𝒪, c * ci = 1 := hcu.exists_right_inv
    haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
    letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
    let mk := Ideal.Quotient.mk (Ideal.span {π})
    let t : 𝒪 ⧸ Ideal.span {π} := mk (-(d * ci))
    have hct : mk c * t = -mk d := by
      show mk c * mk (-(d * ci)) = -mk d
      rw [← map_mul, mul_neg, ← mul_assoc, mul_comm c d, mul_assoc, hci, mul_one, map_neg]
    have ht : t ^ r = t := by
      letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
      have h := FiniteField.pow_card t
      rw [← Nat.card_eq_fintype_card, hres] at h
      exact h
    have hroot : (X ^ r - X : (𝒪 ⧸ Ideal.span {π})[X]).IsRoot t := by
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      exact sub_eq_zero.mpr ht
    have hdvd : (C c * X + C d : 𝒪[X]).map mk ∣ (C c * (X ^ r - X) : 𝒪[X]).map mk := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
      have e : (C (mk c) * X + C (mk d) : (𝒪 ⧸ Ideal.span {π})[X]) = C (mk c) * (X - C t) := by
        rw [mul_sub, ← C_mul, hct, C_neg, sub_neg_eq_add]
      rw [e]
      exact mul_dvd_mul_left _ (Polynomial.dvd_iff_isRoot.mpr hroot)
    obtain ⟨q, s, hqs⟩ := exists_mul_add_C_mul_of_map_dvd π _ _ hdvd
    have hw : IsUnit (aeval ζ (C c * (X ^ r - X) : 𝒪[X])) := by
      rw [map_mul, Polynomial.aeval_C, map_sub, map_pow, Polynomial.aeval_X]
      exact (hcu.map _).mul hζ
    have := isUnit_aeval_of_eq_mul_add π hA ζ _ q s _ hqs hw
    rwa [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C] at this

end Units

theorem row_not_mem_or {𝒪 : Type} [CommRing 𝒪] (M : GL (Fin 2) 𝒪) (I : Ideal 𝒪) (hI : I ≠ ⊤) (i : Fin 2) :
    (M : Matrix (Fin 2) (Fin 2) 𝒪) i 0 ∉ I ∨ (M : Matrix (Fin 2) (Fin 2) 𝒪) i 1 ∉ I := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : ((M * M⁻¹ : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) i i = 1 := by
    rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e
  rw [← e]
  exact I.add_mem (I.mul_mem_right _ h.1) (I.mul_mem_right _ h.2)

section ForcedLine

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def unitK (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (π : 𝒪) (hπ0 : π ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap 𝒪 K π) (fun h => hπ0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h))

@[scoped simp] theorem unitK_coe (π : 𝒪) (hπ0 : π ≠ 0) : ((unitK K π hπ0 : Kˣ) : K) = algebraMap 𝒪 K π := rfl

variable (π : 𝒪) (hπ0 : π ≠ 0)
variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])

include hg₁ in
theorem g₁_mulVec (w : Fin 2 → K) : (g₁ : Matrix (Fin 2) (Fin 2) K).mulVec w = ![algebraMap 𝒪 K π * w 0, w 1] := by
  rw [hg₁]
  ext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

include hg₁ in

theorem act_g₁_le : (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  rw [g₁_mulVec π g₁ hg₁]
  intro i; fin_cases i
  · obtain ⟨a, ha⟩ := hw 0
    exact ⟨π * a, by simp [← ha, map_mul]⟩
  · simpa using hw 1

include hg₁ in

theorem act_pi_le_act_g₁ :
    (FullLattice.act (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K)).1 ≤
      (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  refine mem_latticeMap.mpr ⟨![w 0, algebraMap 𝒪 K π * w 1], ?_, ?_⟩
  · intro i; fin_cases i
    · simpa using hw 0
    · obtain ⟨a, ha⟩ := hw 1
      exact ⟨π * a, by simp [← ha, map_mul]⟩
  · rw [g₁_mulVec π g₁ hg₁, scalarGL_mulVec, unitK_coe]
    ext i
    fin_cases i <;> simp

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

include hg₁ in

theorem incl_act_g₁ (α β : B) :
    inclBaseChange B (act_g₁_le π g₁ hg₁) (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)
      (α ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + β ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)) =
      (algebraMap 𝒪 B π * α) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + β ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 := by
  rw [map_add, map_add, actBaseChange_tmul, actBaseChange_tmul]
  erw [inclBaseChange_tmul, inclBaseChange_tmul]
  rw [show (algebraMap 𝒪 B π * α) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 = α ⊗ₜ[𝒪] (π • stdBasisVec (𝒪 := 𝒪) K 0) by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]]
  congr 1 <;> congr 1 <;> apply Subtype.ext
  · show ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) :
      ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((π • stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [coe_latticeMapEquiv_apply, g₁_mulVec π g₁ hg₁, Submodule.coe_smul]
    ext i
    fin_cases i <;> simp [stdBasisVec, Algebra.smul_def]
  · show ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
      ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [coe_latticeMapEquiv_apply, g₁_mulVec π g₁ hg₁]
    ext i
    fin_cases i <;> simp [stdBasisVec]

include hg₁ in

theorem incl_act_pi (ζ : B) :
    inclBaseChange B (act_pi_le_act_g₁ π hπ0 g₁ hg₁)
      (actBaseChange B (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K)
        (ζ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)) =
      actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)
        (ζ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
  rw [map_add, map_add, actBaseChange_tmul, actBaseChange_tmul, map_add, actBaseChange_tmul, actBaseChange_tmul]
  erw [inclBaseChange_tmul, inclBaseChange_tmul]
  congr 1
  · congr 1
    apply Subtype.ext
    show ((latticeMapEquiv (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) :
      ↥(FullLattice.act (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) :
      ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
    rw [coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, g₁_mulVec π g₁ hg₁, scalarGL_mulVec, unitK_coe]
    ext i
    fin_cases i <;> simp [stdBasisVec]
  · refine Eq.trans (b := (1 : B) ⊗ₜ[𝒪] (π • latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1)))
      ?_ ?_
    · congr 1
      apply Subtype.ext
      show ((latticeMapEquiv (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
        ↥(FullLattice.act (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
        ((π • latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
          ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
      rw [Submodule.coe_smul, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, g₁_mulVec π g₁ hg₁, scalarGL_mulVec,
        unitK_coe]
      ext i
      fin_cases i <;> simp [stdBasisVec, Algebra.smul_def]
    · rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl

include hπ0 hg₁ in

theorem line_act_g₁_eq (d : DeligneDatum (K := K) π B) (ζ : B) (hζ : IsUnit ζ)
    (h0 : d.line (stdFullLattice K) =
      Submodule.span B {ζ ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1}) :
    d.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {ζ ⊗ₜ[𝒪] stdBasisVec K 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice K)).toLinearMap := by
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe]
  apply le_antisymm
  · intro x hx
    obtain ⟨x₀, rfl⟩ := (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)).surjective x
    have hx' : inclBaseChange B (act_g₁_le π g₁ hg₁) (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K) x₀) ∈
        d.line (stdFullLattice K) :=
      d.mono (act_g₁_le π g₁ hg₁) (Submodule.mem_map_of_mem hx)
    obtain ⟨α, β, rfl⟩ : ∃ α β : B, x₀ = α ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + β ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 := by
      refine ⟨coord B 0 x₀, coord B 1 x₀, ?_⟩
      conv_lhs => rw [eq_sum_coord B x₀]
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    rw [incl_act_g₁ π g₁ hg₁, h0] at hx'
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx'
    have e0 := congrArg (coord B 0) ht
    have e1 := congrArg (coord B 1) ht
    simp only [map_smul, map_add, coord_tmul_stdBasisVec, smul_eq_mul, if_pos, if_neg (show (0 : Fin 2) ≠ 1 by decide),
      if_neg (show (1 : Fin 2) ≠ 0 by decide), add_zero, zero_add, mul_one] at e0 e1

    refine Submodule.mem_span_singleton.mpr ⟨α * ↑hζ.unit⁻¹, ?_⟩
    rw [← map_smul, smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      mul_assoc, IsUnit.val_inv_mul, mul_one]
    have et : α * ↑hζ.unit⁻¹ * algebraMap 𝒪 B π = β := by
      calc α * ↑hζ.unit⁻¹ * algebraMap 𝒪 B π = algebraMap 𝒪 B π * α * ↑hζ.unit⁻¹ := by ring
        _ = t * ζ * ↑hζ.unit⁻¹ := by rw [e0]
        _ = β := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one, e1]
    rw [et]
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← incl_act_pi π hπ0 g₁ hg₁]
    refine d.mono (act_pi_le_act_g₁ π hπ0 g₁ hg₁) (Submodule.mem_map_of_mem ?_)
    rw [d.homothety (unitK K π hπ0) (stdFullLattice K), h0]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)

end ForcedLine

section Moebius

open Polynomial

theorem isUnit_add_of_isNilpotent {A : Type} [CommRing A] {u x : A} (hu : IsUnit u) (hx : IsNilpotent x) :
    IsUnit (u + x) := by
  obtain ⟨u, rfl⟩ := hu
  rw [show (u : A) + x = u * (1 + ↑u⁻¹ * x) by rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]]
  exact (Units.isUnit u).mul (IsNilpotent.isUnit_one_add (Commute.isNilpotent_mul_left (Commute.all _ _) hx))

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

theorem residue_charP_and_pow (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) :
    CharP (𝒪 ⧸ Ideal.span {π}) r ∧ ∀ x : 𝒪 ⧸ Ideal.span {π}, x ^ r = x := by
  haveI := hdvr
  haveI hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by rw [← Nat.card_eq_fintype_card, hres]
  refine ⟨charP_of_card_eq_prime hcard, fun x => ?_⟩
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have h := FiniteField.pow_card x
  rw [hcard] at h
  exact h

theorem map_frobDiff_eq_zero (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (a b c d : 𝒪) :
    ((C a * X + C b) ^ r * (C c * X + C d) - (C a * X + C b) * (C c * X + C d) ^ r -
        C (a * d - b * c) * (X ^ r - X) : 𝒪[X]).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
  obtain ⟨hchar, hpow⟩ := residue_charP_and_pow hdvr π hπ hres
  haveI := hchar
  set mk := Ideal.Quotient.mk (Ideal.span {π})
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_X]
  rw [add_pow_char (C (mk a) * X) (C (mk b)) r, add_pow_char (C (mk c) * X) (C (mk d)) r, mul_pow, mul_pow, ← C_pow, ← C_pow,
    ← C_pow, ← C_pow, hpow, hpow, hpow, hpow, map_sub mk, map_mul mk, map_mul mk, C_sub, C_mul, C_mul]
  ring

theorem isUnit_frobDiff (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    {A : Type} [CommRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π)) (ζ : A) (hζ : IsUnit (ζ ^ r - ζ))
    (a b c d : 𝒪) (hdet : IsUnit (a * d - b * c)) :
    IsUnit ((algebraMap 𝒪 A a * ζ + algebraMap 𝒪 A b) ^ r * (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) -
      (algebraMap 𝒪 A a * ζ + algebraMap 𝒪 A b) * (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) ^ r) := by
  set G : 𝒪[X] := (C a * X + C b) ^ r * (C c * X + C d) - (C a * X + C b) * (C c * X + C d) ^ r -
    C (a * d - b * c) * (X ^ r - X) with hG
  have hker : G ∈ RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span {π}))) := by
    rw [RingHom.mem_ker, Polynomial.coe_mapRingHom, hG]
    exact map_frobDiff_eq_zero hdvr π hπ hres a b c d
  rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hker
  obtain ⟨S, hS⟩ := Ideal.mem_span_singleton'.mp hker
  have e : (algebraMap 𝒪 A a * ζ + algebraMap 𝒪 A b) ^ r * (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) -
      (algebraMap 𝒪 A a * ζ + algebraMap 𝒪 A b) * (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) ^ r =
      algebraMap 𝒪 A (a * d - b * c) * (ζ ^ r - ζ) + algebraMap 𝒪 A π * aeval ζ S := by
    have h1 : aeval ζ G = algebraMap 𝒪 A π * aeval ζ S := by
      rw [← hS, map_mul, Polynomial.aeval_C, mul_comm]
    rw [hG] at h1
    simp only [map_sub, map_mul, map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X] at h1
    have h2 := sub_eq_iff_eq_add'.mp h1
    rw [← map_mul (algebraMap 𝒪 A), ← map_mul (algebraMap 𝒪 A), ← map_sub (algebraMap 𝒪 A)] at h2
    exact h2
  rw [e]
  exact isUnit_add_of_isNilpotent ((hdet.map (algebraMap 𝒪 A)).mul hζ)
    (Commute.isNilpotent_mul_right (Commute.all _ _) hA)

variable {A : Type} [CommRing A] [Algebra 𝒪 A]

def num (M : GL (Fin 2) 𝒪) (z : A) : A :=
  algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * z + algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1)

def den (M : GL (Fin 2) 𝒪) (z : A) : A :=
  algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * z + algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1)

theorem map_num {C : Type} [CommRing C] [Algebra 𝒪 C] (f : A →ₐ[𝒪] C) (M : GL (Fin 2) 𝒪) (z : A) :
    f (num M z) = num M (f z) := by
  simp only [num, map_add, map_mul, AlgHom.commutes]

theorem map_den {C : Type} [CommRing C] [Algebra 𝒪 C] (f : A →ₐ[𝒪] C) (M : GL (Fin 2) 𝒪) (z : A) :
    f (den M z) = den M (f z) := by
  simp only [den, map_add, map_mul, AlgHom.commutes]

omit [IsDomain 𝒪] in
theorem span_singleton_ne_top_of_irreducible {π : 𝒪} (hπ : Irreducible π) : Ideal.span {π} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit

theorem isUnit_den (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hA : IsNilpotent (algebraMap 𝒪 A π)) (z : A) (hz : IsUnit (z ^ r - z))
    (M : GL (Fin 2) 𝒪) : IsUnit (den M z) :=
  isUnit_linear hdvr π hπ hres hA z hz _ _ (row_not_mem_or M _ (span_singleton_ne_top_of_irreducible hπ) 1)

theorem isUnit_num (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hA : IsNilpotent (algebraMap 𝒪 A π)) (z : A) (hz : IsUnit (z ^ r - z))
    (M : GL (Fin 2) 𝒪) : IsUnit (num M z) :=
  isUnit_linear hdvr π hπ hres hA z hz _ _ (row_not_mem_or M _ (span_singleton_ne_top_of_irreducible hπ) 0)

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem isUnit_det (M : GL (Fin 2) 𝒪) :
    IsUnit ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) := by
  rw [← Matrix.det_fin_two]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)

theorem isUnit_pow_sub_of_mul_den_eq_num (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hA : IsNilpotent (algebraMap 𝒪 A π)) (z : A) (hz : IsUnit (z ^ r - z)) (M : GL (Fin 2) 𝒪)
    (z' : A) (hD : IsUnit (den M z)) (hz' : z' * den M z = num M z) : IsUnit (z' ^ r - z') := by
  have hF := isUnit_frobDiff hdvr π hπ hres hA z hz _ _ _ _ (isUnit_det M)
  have e : (z' ^ r - z') * den M z ^ (r + 1) = num M z ^ r * den M z - num M z * den M z ^ r := by
    rw [← hz']; ring
  have : IsUnit ((z' ^ r - z') * den M z ^ (r + 1)) := by
    rw [e]; exact hF
  exact isUnit_of_mul_isUnit_left this

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem inv_mul_entry (M : GL (Fin 2) 𝒪) (i j : Fin 2) :
    algebraMap 𝒪 A (((M⁻¹ : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) i 0) *
        algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 j) +
      algebraMap 𝒪 A (((M⁻¹ : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) i 1) *
        algebraMap 𝒪 A ((M : Matrix (Fin 2) (Fin 2) 𝒪) 1 j) =
      if i = j then 1 else 0 := by
  have e : ((M⁻¹ * M : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) i j = if i = j then 1 else 0 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e
  rw [← map_mul, ← map_mul, ← map_add, e]
  split_ifs <;> simp

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem den_num_inv_of_mul_den_eq_num (M : GL (Fin 2) 𝒪) (z z' : A) (hz' : z' * den M z = num M z) :
    den M⁻¹ z' * den M z = 1 ∧ num M⁻¹ z' * den M z = z := by
  have e10 := inv_mul_entry (A := A) M 1 0
  have e11 := inv_mul_entry (A := A) M 1 1
  have e00 := inv_mul_entry (A := A) M 0 0
  have e01 := inv_mul_entry (A := A) M 0 1
  simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide), if_pos, if_neg (show (0 : Fin 2) ≠ 1 by decide)] at e10 e11 e00 e01
  simp only [num, den] at hz' ⊢
  constructor
  · linear_combination (algebraMap 𝒪 A (((M⁻¹ : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) 1 0)) * hz' + z * e10 + e11
  · linear_combination (algebraMap 𝒪 A (((M⁻¹ : GL (Fin 2) 𝒪) : Matrix (Fin 2) (Fin 2) 𝒪) 0 0)) * hz' + z * e00 + e01

end Moebius

section Tau

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

abbrev Avn (𝒪 : Type) [CommRing 𝒪] (r : ℕ) (π : 𝒪) (n : ℕ) : Type :=
  chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev zetaA (𝒪 : Type) [CommRing 𝒪] (r : ℕ) (π : 𝒪) (n : ℕ) : Avn 𝒪 r π n :=
  Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) (chartVRing.ζ 𝒪 r)

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem isNilpotent_algebraMap_Avn (π : 𝒪) (n : ℕ) : IsNilpotent (algebraMap 𝒪 (Avn 𝒪 r π n) π) :=
  isNilpotent_algebraMap_modPow π (chartVRing 𝒪 r) n

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem algebraMap_pow_eq_zero (π : 𝒪) (n : ℕ) : algebraMap 𝒪 (Avn 𝒪 r π n) π ^ (n + 1) = 0 := by
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (chartVRing 𝒪 r) (Avn 𝒪 r π n), Ideal.Quotient.algebraMap_eq, map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem isUnit_zetaA_pow_sub (π : 𝒪) (n : ℕ) : IsUnit (zetaA 𝒪 r π n ^ r - zetaA 𝒪 r π n) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
  rwa [map_sub, map_pow] at h

omit [IsDomain 𝒪] in
theorem isUnit_zetaA (π : 𝒪) (n : ℕ) : IsUnit (zetaA 𝒪 r π n) := by
  have h := isUnit_zetaA_pow_sub (r := r) π n
  rw [show zetaA 𝒪 r π n ^ r - zetaA 𝒪 r π n = zetaA 𝒪 r π n * (zetaA 𝒪 r π n ^ (r - 1) - 1) by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (Fact.out : r.Prime).one_lt.le]] at h
  exact isUnit_of_mul_isUnit_left h

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem algHom_ext_Avn (π : 𝒪) (n : ℕ) {C : Type} [CommRing C] [Algebra 𝒪 C] (f g : Avn 𝒪 r π n →ₐ[𝒪] C)
    (h : f (zetaA 𝒪 r π n) = g (zetaA 𝒪 r π n)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (Submonoid.powers (vertexDiscr 𝒪 r))
  apply Polynomial.algHom_ext
  exact h

omit [Fact r.Prime] [IsDomain 𝒪] in

def liftHom (π : 𝒪) (n : ℕ) (x : Avn 𝒪 r π n) (hx : IsUnit (x ^ r - x)) : Avn 𝒪 r π n →ₐ[𝒪] Avn 𝒪 r π n :=
  Ideal.Quotient.liftₐ (Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)})
    (chartVRing.lift (⟨x, hx⟩ : (chartV 𝒪 r).obj (Avn 𝒪 r π n))) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_pow, AlgHom.commutes, algebraMap_pow_eq_zero, mul_zero])

omit [Fact r.Prime] [IsDomain 𝒪] in
@[scoped simp] theorem liftHom_zetaA (π : 𝒪) (n : ℕ) (x : Avn 𝒪 r π n) (hx : IsUnit (x ^ r - x)) :
    liftHom π n x hx (zetaA 𝒪 r π n) = x := by
  show Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)) = x
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact chartVRing.lift_ζ _

variable (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (n : ℕ)

def moeb (M : GL (Fin 2) 𝒪) : Avn 𝒪 r π n :=
  num M (zetaA 𝒪 r π n) *
    ↑(isUnit_den hdvr π hπ hres (isNilpotent_algebraMap_Avn π n) (zetaA 𝒪 r π n) (isUnit_zetaA_pow_sub π n) M).unit⁻¹

theorem moeb_mul_den (M : GL (Fin 2) 𝒪) :
    moeb hdvr π hπ hres n M * den M (zetaA 𝒪 r π n) = num M (zetaA 𝒪 r π n) := by
  rw [moeb, mul_assoc, IsUnit.val_inv_mul, mul_one]

theorem isUnit_moeb_pow_sub (M : GL (Fin 2) 𝒪) : IsUnit (moeb hdvr π hπ hres n M ^ r - moeb hdvr π hπ hres n M) :=
  isUnit_pow_sub_of_mul_den_eq_num hdvr π hπ hres (isNilpotent_algebraMap_Avn π n) _ (isUnit_zetaA_pow_sub π n) M _
    (isUnit_den hdvr π hπ hres (isNilpotent_algebraMap_Avn π n) _ (isUnit_zetaA_pow_sub π n) M) (moeb_mul_den hdvr π hπ hres n M)

def tauHom (M : GL (Fin 2) 𝒪) : Avn 𝒪 r π n →ₐ[𝒪] Avn 𝒪 r π n :=
  liftHom π n (moeb hdvr π hπ hres n M) (isUnit_moeb_pow_sub hdvr π hπ hres n M)

theorem tauHom_zetaA (M : GL (Fin 2) 𝒪) : tauHom hdvr π hπ hres n M (zetaA 𝒪 r π n) = moeb hdvr π hπ hres n M :=
  liftHom_zetaA π n _ _

theorem tauHom_zetaA_mul_den (M : GL (Fin 2) 𝒪) :
    tauHom hdvr π hπ hres n M (zetaA 𝒪 r π n) * den M (zetaA 𝒪 r π n) = num M (zetaA 𝒪 r π n) := by
  rw [tauHom_zetaA, moeb_mul_den]

theorem tauHom_inv_comp (M : GL (Fin 2) 𝒪) :
    (tauHom hdvr π hπ hres n M⁻¹).comp (tauHom hdvr π hπ hres n M) = AlgHom.id 𝒪 (Avn 𝒪 r π n) := by
  apply algHom_ext_Avn
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  set φ := tauHom hdvr π hπ hres n M⁻¹ with hφ
  set z := zetaA 𝒪 r π n with hz

  have hw : φ z * den M⁻¹ z = num M⁻¹ z := tauHom_zetaA_mul_den hdvr π hπ hres n M⁻¹

  obtain ⟨h1, h2⟩ := den_num_inv_of_mul_den_eq_num M⁻¹ z (φ z) hw
  rw [inv_inv] at h1 h2

  have h3 : φ (tauHom hdvr π hπ hres n M z) * den M (φ z) = num M (φ z) := by
    rw [← map_den φ, ← map_num φ, ← map_mul, tauHom_zetaA_mul_den]
  calc φ (tauHom hdvr π hπ hres n M z)
      = φ (tauHom hdvr π hπ hres n M z) * (den M (φ z) * den M⁻¹ z) := by rw [h1, mul_one]
    _ = num M (φ z) * den M⁻¹ z := by rw [← mul_assoc, h3]
    _ = z := h2

def tau (M : GL (Fin 2) 𝒪) : Avn 𝒪 r π n ≃ₐ[𝒪] Avn 𝒪 r π n :=
  AlgEquiv.ofAlgHom (tauHom hdvr π hπ hres n M) (tauHom hdvr π hπ hres n M⁻¹)
    (by have h := tauHom_inv_comp hdvr π hπ hres n M⁻¹; rwa [inv_inv] at h)
    (tauHom_inv_comp hdvr π hπ hres n M)

theorem tau_zetaA_mul_den (M : GL (Fin 2) 𝒪) :
    tau hdvr π hπ hres n M (zetaA 𝒪 r π n) * den M (zetaA 𝒪 r π n) = num M (zetaA 𝒪 r π n) :=
  tauHom_zetaA_mul_den hdvr π hπ hres n M

end Tau

section PullbackLine

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

omit [IsFractionRing 𝒪 K] in
theorem scalarGL_inv' (c : Kˣ) : (scalarGL c : GL (Fin 2) K)⁻¹ = scalarGL c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one]

omit [IsFractionRing 𝒪 K] in

theorem inv_mul_scalarGL_inv_mul (g : GL (Fin 2) K) (c : Kˣ) : g⁻¹ * (scalarGL c)⁻¹ * g = (scalarGL c)⁻¹ := by
  have hc : Commute (scalarGL c) g := scalarGL_mul_comm c g
  rw [mul_assoc, hc.inv_left.eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_map_eq_of_act_eq (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K)) :
    ∃ hO : GL (Fin 2) 𝒪, Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g := by
  have h1 : latticeMap g (stdLattice 𝒪 K) = latticeMap (scalarGL c) (stdLattice 𝒪 K) := congrArg Subtype.val hg
  have h2 : latticeMap ((scalarGL c)⁻¹ * g) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, h1, latticeMap_inv_latticeMap]
  exact MonoidHom.mem_range.mp ((latticeMap_stdLattice_eq_iff_mem_range _).mp h2)

omit [IsFractionRing 𝒪 K] in

theorem act_scalarGL_inv_val_eq (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K)) :
    (FullLattice.act (scalarGL c⁻¹) (stdFullLattice (𝒪 := 𝒪) K)).1 = (FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  have h1 : latticeMap g (stdLattice 𝒪 K) = latticeMap (scalarGL c) (stdLattice 𝒪 K) := congrArg Subtype.val hg
  show latticeMap (scalarGL c⁻¹) (stdLattice 𝒪 K) = latticeMap g⁻¹ (stdLattice 𝒪 K)
  rw [← scalarGL_inv', ← inv_mul_scalarGL_inv_mul g c, latticeMap_mul, latticeMap_mul, h1, latticeMap_inv_latticeMap]

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

omit [IsFractionRing 𝒪 K] in

theorem scalarGL_inv_mulVec (g : GL (Fin 2) K) (c : Kˣ) (hO : GL (Fin 2) 𝒪)
    (hhO : Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g) (v : Fin 2 → K) :
    ((scalarGL c⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v =
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hhO, ← mul_assoc, inv_mul_scalarGL_inv_mul, scalarGL_inv']

theorem ofEq_latticeMapEquiv_eq (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K))
    (hO : GL (Fin 2) 𝒪) (hhO : Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g) (j : Fin 2) :
    (LinearEquiv.ofEq _ _ (act_scalarGL_inv_val_eq g c hg)
        (latticeMapEquiv (scalarGL c⁻¹) (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K j)) :
        ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) =
      ((hO : Matrix (Fin 2) (Fin 2) 𝒪) 0 j • latticeMapEquiv g⁻¹ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) +
        (hO : Matrix (Fin 2) (Fin 2) 𝒪) 1 j • latticeMapEquiv g⁻¹ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
        ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) := by
  apply Subtype.ext
  rw [coe_ofEq_apply, coe_latticeMapEquiv_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, scalarGL_inv_mulVec g c hO hhO, ← Matrix.mulVec_smul,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 1
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [stdBasisVec, Matrix.mulVec, Matrix.GeneralLinearGroup.map_apply, Algebra.smul_def]

omit [IsFractionRing 𝒪 K] in

theorem tmul_comb {M : Type} [AddCommGroup M] [Module 𝒪 M] (ζ : B) (a b c d : 𝒪) (x y : M) :
    ζ ⊗ₜ[𝒪] (a • x + c • y) + (1 : B) ⊗ₜ[𝒪] (b • x + d • y) =
      (algebraMap 𝒪 B a * ζ + algebraMap 𝒪 B b) ⊗ₜ[𝒪] x + (algebraMap 𝒪 B c * ζ + algebraMap 𝒪 B d) ⊗ₜ[𝒪] y := by
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.add_tmul,
    Algebra.smul_def, mul_one]
  abel

theorem line_pullback_inv_std (π : 𝒪) (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K))
    (hO : GL (Fin 2) 𝒪) (hhO : Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g)
    (d : DeligneDatum (K := K) π B) (ζ : B)
    (h0 : d.line (stdFullLattice K) =
      Submodule.span B {ζ ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1}) :
    (DeligneDatum.pullback π B g⁻¹ d).line (stdFullLattice K) =
      Submodule.span B {num hO ζ ⊗ₜ[𝒪] stdBasisVec K 0 + den hO ζ ⊗ₜ[𝒪] stdBasisVec K 1} := by
  show (d.line (FullLattice.act g⁻¹ (stdFullLattice K))).comap (actBaseChange B g⁻¹ (stdFullLattice K)).toLinearMap = _
  rw [DeligneDatum.line_transport π d (act_scalarGL_inv_val_eq g c hg), d.homothety c⁻¹ (stdFullLattice K), h0,
    Submodule.map_span, Set.image_singleton, Submodule.map_span, Set.image_singleton, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_span, Set.image_singleton]
  congr 2
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, map_add, map_add,
    actBaseChange_tmul, actBaseChange_tmul, map_add, actBaseChange_tmul, actBaseChange_tmul]
  erw [transportEquiv_tmul, transportEquiv_tmul, ofEq_latticeMapEquiv_eq g c hg hO hhO 0, ofEq_latticeMapEquiv_eq g c hg hO hhO 1]
  exact tmul_comb ζ _ _ _ _ _ _

end PullbackLine

section Main

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
variable (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
variable (n : ℕ)

def IsChartDatum {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (ξ : B) : Prop :=
  d.line (stdFullLattice K) = Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
  d.line (FullLattice.act g₁ (stdFullLattice K)) =
    (Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec K 0 + (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K 1}).map
      (actBaseChange B g₁ (stdFullLattice K)).toLinearMap ∧
  d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K)

include hdvr hπ hres hg₁ in

theorem exists_isChartDatum (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ξ : B) (hξ : IsUnit (ξ ^ r - ξ)) : ∃ d : DeligneDatum (K := K) π B, IsChartDatum π g₁ d ξ := by
  haveI := hdvr
  have hr2 := (Fact.out : r.Prime).two_le
  have hfac : ξ ^ r - ξ = ξ * (ξ ^ (r - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (Fact.out : r.Prime).one_lt.le]
  have hξu : IsUnit ξ := isUnit_of_mul_isUnit_left (hfac ▸ hξ)
  have hξ1 : IsUnit (ξ ^ (r - 1) - 1) := isUnit_of_mul_isUnit_right (hfac ▸ hξ)
  set η : B := ↑hξu.unit⁻¹ * algebraMap 𝒪 B π with hη
  have hξη : ξ * η = algebraMap 𝒪 B π := by rw [hη, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hηn : IsNilpotent η := Commute.isNilpotent_mul_left (Commute.all _ _) hB
  obtain ⟨k, hk⟩ : ∃ k, r - 1 = k + 1 := ⟨r - 2, by omega⟩
  have hη1 : IsUnit (η ^ (r - 1) - 1) := by
    rw [hk]
    exact (hηn.pow_succ k).isUnit_sub_one
  obtain ⟨d, h0, h1, h2⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    (K := K) π hπ r hres g₁ hg₁ B hB (chartERing.lift (⟨(ξ, η), hξη, hξ1, hη1⟩ : (chartE 𝒪 π r).obj B))
  rw [chartERing.lift_ξ] at h0
  rw [chartERing.lift_η] at h1
  refine ⟨d, h0, ?_, h2⟩
  rw [h1, ← Submodule.span_singleton_smul_eq hξu (_ + _), smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    smul_eq_mul, smul_eq_mul, mul_one]
  show Submodule.map _ (Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec K 0 + (ξ * η) ⊗ₜ[𝒪] stdBasisVec K 1}) = _
  rw [hξη]

include hdvr hπ hres hg₁ in

theorem isPullback_of_isChartDatum (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K))
    (hO : GL (Fin 2) 𝒪) (hhO : Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (y : Avn 𝒪 r π n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B)
    (hd : IsChartDatum π g₁ d (y (zetaA 𝒪 r π n)))
    (hd' : IsChartDatum π g₁ d' (y (tau hdvr π hπ hres n hO (zetaA 𝒪 r π n)))) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d' := by
  haveI := hdvr
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hB : IsNilpotent (algebraMap 𝒪 B π) := by
    rw [← y.commutes π]; exact (isNilpotent_algebraMap_Avn π n).map y
  have hζ : IsUnit (y (zetaA 𝒪 r π n) ^ r - y (zetaA 𝒪 r π n)) := by
    have h := (isUnit_zetaA_pow_sub (r := r) π n).map y
    rwa [map_sub, map_pow] at h
  have hD : IsUnit (den hO (y (zetaA 𝒪 r π n))) := isUnit_den hdvr π hπ hres hB _ hζ hO
  have hζ' : y (tau hdvr π hπ hres n hO (zetaA 𝒪 r π n)) * den hO (y (zetaA 𝒪 r π n)) = num hO (y (zetaA 𝒪 r π n)) := by
    have h := congrArg y (tau_zetaA_mul_den hdvr π hπ hres n hO)
    rwa [map_mul, map_den, map_num] at h
  have hζ'u : IsUnit (y (tau hdvr π hπ hres n hO (zetaA 𝒪 r π n))) :=
    ((isUnit_zetaA (r := r) π n).map (tau hdvr π hπ hres n hO)).map y
  have e0 : (DeligneDatum.pullback π B g⁻¹ d).line (stdFullLattice K) =
      Submodule.span B {y (tau hdvr π hπ hres n hO (zetaA 𝒪 r π n)) ⊗ₜ[𝒪] stdBasisVec K 0 +
        (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} := by
    rw [line_pullback_inv_std π g c hg hO hhO d _ hd.1, ← Submodule.span_singleton_smul_eq hD (_ ⊗ₜ[𝒪] _ + (1 : B) ⊗ₜ[𝒪] _),
      smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,
      mul_comm (den hO (y (zetaA 𝒪 r π n))), hζ']
  have e1 := line_act_g₁_eq π hπ0 g₁ hg₁ (DeligneDatum.pullback π B g⁻¹ d) _ hζ'u e0
  have heq : DeligneDatum.pullback π B g⁻¹ d = d' :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d' (DeligneDatum.pullback π B g⁻¹ d)
      (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K) hd'.2.2 (e0.trans hd'.1.symm) (e1.trans hd'.2.1.symm)
  rw [← heq]
  exact DeligneDatum.isPullback_pullback π B g⁻¹ d

include hdvr hπ hres hg₁ in

theorem eq_tau_of_forall (g : GL (Fin 2) K) (c : Kˣ)
    (hg : FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K))
    (hO : GL (Fin 2) 𝒪) (hhO : Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) hO = (scalarGL c)⁻¹ * g)
    (τ₁ : Avn 𝒪 r π n ≃ₐ[𝒪] Avn 𝒪 r π n)
    (hτ₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (y : Avn 𝒪 r π n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B),
      IsChartDatum π g₁ d (y (zetaA 𝒪 r π n)) → IsChartDatum π g₁ d' (y (τ₁ (zetaA 𝒪 r π n))) →
        DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d') :
    τ₁ = tau hdvr π hπ hres n hO := by
  have hz := isUnit_zetaA_pow_sub (r := r) π n
  obtain ⟨d, hd⟩ := exists_isChartDatum hdvr π hπ hres g₁ hg₁ (Avn 𝒪 r π n) (isNilpotent_algebraMap_Avn π n) _ hz
  obtain ⟨d₁, hd₁⟩ := exists_isChartDatum hdvr π hπ hres g₁ hg₁ (Avn 𝒪 r π n) (isNilpotent_algebraMap_Avn π n)
    (τ₁ (zetaA 𝒪 r π n)) (by have h := hz.map τ₁; rwa [map_sub, map_pow] at h)
  obtain ⟨d₂, hd₂⟩ := exists_isChartDatum hdvr π hπ hres g₁ hg₁ (Avn 𝒪 r π n) (isNilpotent_algebraMap_Avn π n)
    (tau hdvr π hπ hres n hO (zetaA 𝒪 r π n)) (by have h := hz.map (tau hdvr π hπ hres n hO); rwa [map_sub, map_pow] at h)
  have h1 := hτ₁ (Avn 𝒪 r π n) (AlgHom.id 𝒪 _) d d₁ hd hd₁ (stdFullLattice K)
  have h2 := isPullback_of_isChartDatum hdvr π hπ hres g₁ hg₁ n g c hg hO hhO (Avn 𝒪 r π n) (AlgHom.id 𝒪 _) d d₂ hd hd₂
    (stdFullLattice K)
  rw [hd₁.1] at h1
  rw [hd₂.1, ← h1] at h2
  have hz' := eq_of_span_tmul_add_one_tmul_eq _ _ _ h2.symm
  apply AlgEquiv.coe_algHom_injective
  exact algHom_ext_Avn π n _ _ hz'

end Main

end F2AlphaE
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq.F2AlphaE"

open F2AlphaE in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (c : K₀ˣ)
    (hg : FullLattice.act g (stdFullLattice K₀) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K₀))
    (n : ℕ) :
    ∃! τ : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) ≃ₐ[𝒪]
        (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}),
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
        (y : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) →ₐ[𝒪] B)
        (d d' : DeligneDatum (K := K₀) π B),
        (d.line (stdFullLattice K₀) =
            Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
                (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        (d'.line (stdFullLattice K₀) =
            Submodule.span B {((y.comp τ.toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {((y.comp τ.toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
                (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' := by
  obtain ⟨hO, hhO⟩ := exists_map_eq_of_act_eq g c hg
  refine ⟨tau hdvr π hπ hres n hO, ?_, ?_⟩
  · intro B _ _ y d d' hd hd'
    exact isPullback_of_isChartDatum hdvr π hπ hres g₁ hg₁ n g c hg hO hhO B y d d' hd hd'
  · intro τ₁ hτ₁
    exact eq_tau_of_forall hdvr π hπ hres g₁ hg₁ n g c hg hO hhO τ₁ (fun B _ _ y d d' hd hd' => hτ₁ B y d d' hd hd')

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq.F2AlphaE"

end S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq (solution)
