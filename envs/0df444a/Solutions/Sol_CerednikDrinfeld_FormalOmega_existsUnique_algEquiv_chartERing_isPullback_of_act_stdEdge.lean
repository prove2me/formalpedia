-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1818ecc5-ac37-59af-943d-2a640b61ff29

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaEdge

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

private def _root_.F2AlphaEdge.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "F2AlphaEdge" "coord"
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

theorem eq_of_span_one_tmul_add_tmul_eq (b b' : B)
    (h : Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}) : b = b' := by
  have hmem : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 ∈
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrArg (coord B 1) ht
  have h0 := congrArg (coord B 0) ht
  simp only [map_smul, map_add, coord_tmul_stdBasisVec, smul_eq_mul] at h0 h1
  simp at h0 h1
  rw [h0, one_mul] at h1
  exact h1.symm

theorem eq_of_map_span_one_tmul_add_tmul_eq (g₁ : GL (Fin 2) K) (b b' : B)
    (h : (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}).map
        (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}).map
        (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap) : b = b' :=
  eq_of_span_one_tmul_add_tmul_eq B b b'
    (Submodule.map_injective_of_injective (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)).injective h)

end Coord

section Units

open Polynomial

theorem isUnit_add_of_isNilpotent {A : Type} [CommRing A] {u x : A} (hu : IsUnit u) (hx : IsNilpotent x) :
    IsUnit (u + x) := by
  obtain ⟨u, rfl⟩ := hu
  rw [show (u : A) + x = u * (1 + ↑u⁻¹ * x) by rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]]
  exact (Units.isUnit u).mul (IsNilpotent.isUnit_one_add (Commute.isNilpotent_mul_left (Commute.all _ _) hx))

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
  exact isUnit_of_mul_isUnit_left (e ▸ isUnit_add_of_isNilpotent hw hn)

theorem isUnit_of_not_mem_span {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (x : 𝒪) (hx : x ∉ Ideal.span {π}) : IsUnit x := by
  haveI := hdvr
  have hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  rw [IsLocalRing.eq_maximalIdeal hmax] at hx
  by_contra hu
  exact hx ((IsLocalRing.mem_maximalIdeal x).mpr hu)

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

theorem residue_facts (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) :
    ∃ _ : Fintype (𝒪 ⧸ Ideal.span {π}), Fintype.card (𝒪 ⧸ Ideal.span {π}) = r ∧ CharP (𝒪 ⧸ Ideal.span {π}) r ∧
      (∀ x : 𝒪 ⧸ Ideal.span {π}, x ^ r = x) ∧ (∀ x : 𝒪 ⧸ Ideal.span {π}, x ≠ 0 → x ^ (r - 1) = 1) := by
  haveI := hdvr
  haveI hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by rw [← Nat.card_eq_fintype_card, hres]
  refine ⟨inferInstance, hcard, charP_of_card_eq_prime hcard, fun x => ?_, fun x hx => ?_⟩
  · letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
    have h := FiniteField.pow_card x
    rw [hcard] at h
    exact h
  · letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    rw [hcard] at h
    exact h

theorem isUnit_linear' (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    {A : Type} [CommRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π))
    (ζ : A) (hζ : IsUnit (ζ ^ (r - 1) - 1)) (c d : 𝒪) (hd : d ∉ Ideal.span {π}) :
    IsUnit (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) := by
  have hdu : IsUnit d := isUnit_of_not_mem_span hdvr π hπ d hd
  by_cases hc : c ∈ Ideal.span {π}
  · obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hc
    rw [add_comm]
    refine isUnit_add_of_isNilpotent (hdu.map _) ?_
    rw [map_mul]
    exact Commute.isNilpotent_mul_right (Commute.all _ _) (Commute.isNilpotent_mul_left (Commute.all _ _) hA)
  · haveI := hdvr
    have hcu : IsUnit c := isUnit_of_not_mem_span hdvr π hπ c hc
    obtain ⟨ci, hci⟩ : ∃ ci : 𝒪, c * ci = 1 := hcu.exists_right_inv
    obtain ⟨_, hcard, _, _, hpow1⟩ := residue_facts hdvr π hπ hres
    let mk := Ideal.Quotient.mk (Ideal.span {π})
    let t : 𝒪 ⧸ Ideal.span {π} := mk (-(d * ci))
    have hct : mk c * t = -mk d := by
      show mk c * mk (-(d * ci)) = -mk d
      rw [← map_mul, mul_neg, ← mul_assoc, mul_comm c d, mul_assoc, hci, mul_one, map_neg]
    have ht0 : t ≠ 0 := by
      intro h0
      apply hd
      have h1 : mk (-(d * ci)) = 0 := h0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.neg_mem_iff] at h1
      have h2 := Ideal.mul_mem_right c _ h1
      rwa [mul_assoc, mul_comm ci c, hci, mul_one] at h2
    have ht : t ^ (r - 1) = 1 := hpow1 t ht0
    have hroot : (X ^ (r - 1) - 1 : (𝒪 ⧸ Ideal.span {π})[X]).IsRoot t := by
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      exact sub_eq_zero.mpr ht
    have hdvd : (C c * X + C d : 𝒪[X]).map mk ∣ (C c * (X ^ (r - 1) - 1) : 𝒪[X]).map mk := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      have e : (C (mk c) * X + C (mk d) : (𝒪 ⧸ Ideal.span {π})[X]) = C (mk c) * (X - C t) := by
        rw [mul_sub, ← C_mul, hct, C_neg, sub_neg_eq_add]
      rw [e]
      exact mul_dvd_mul_left _ (Polynomial.dvd_iff_isRoot.mpr hroot)
    obtain ⟨q, s, hqs⟩ := exists_mul_add_C_mul_of_map_dvd π _ _ hdvd
    have hw : IsUnit (aeval ζ (C c * (X ^ (r - 1) - 1) : 𝒪[X])) := by
      rw [map_mul, Polynomial.aeval_C, map_sub, map_pow, Polynomial.aeval_X, map_one]
      exact (hcu.map _).mul hζ
    have := isUnit_aeval_of_eq_mul_add π hA ζ _ q s _ hqs hw
    rwa [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C] at this

theorem map_frob2_eq_zero (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (a e c d : 𝒪) (ha : a ∉ Ideal.span {π}) (he : e ∈ Ideal.span {π}) :
    ((C a * X + C e) ^ (r - 1) * (C c * X + C d) - (C c * X + C d) ^ r - C d * (X ^ (r - 1) - 1) : 𝒪[X]).map
      (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
  obtain ⟨_, hcard, hchar, hpow, hpow1⟩ := residue_facts hdvr π hπ hres
  haveI := hchar
  set mk := Ideal.Quotient.mk (Ideal.span {π}) with hmk
  have he0 : mk e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr he
  have ha0 : mk a ≠ 0 := fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, (Nat.sub_add_cancel (Fact.out : r.Prime).one_lt.le).symm⟩
  have hk' : r - 1 = k := by omega
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_one, he0, C_0, add_zero]
  have h1 : (C (mk c) * X + C (mk d) : (𝒪 ⧸ Ideal.span {π})[X]) ^ r = C (mk c) * X ^ r + C (mk d) := by
    rw [add_pow_char _ _ r, mul_pow, ← C_pow, ← C_pow, hpow, hpow]
  have h2 : (C (mk a) * X : (𝒪 ⧸ Ideal.span {π})[X]) ^ (r - 1) = X ^ (r - 1) := by
    rw [mul_pow, ← C_pow, hpow1 _ ha0, C_1, one_mul]
  rw [h1, h2, hk', hk]
  ring

theorem isUnit_frob2 (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) {A : Type} [CommRing A] [Algebra 𝒪 A] (hA : IsNilpotent (algebraMap 𝒪 A π))
    (ζ : A) (hζ : IsUnit (ζ ^ (r - 1) - 1)) (a e c d : 𝒪) (ha : a ∉ Ideal.span {π}) (he : e ∈ Ideal.span {π})
    (hd : d ∉ Ideal.span {π}) :
    IsUnit ((algebraMap 𝒪 A a * ζ + algebraMap 𝒪 A e) ^ (r - 1) * (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) -
      (algebraMap 𝒪 A c * ζ + algebraMap 𝒪 A d) ^ r) := by
  set G : 𝒪[X] := (C a * X + C e) ^ (r - 1) * (C c * X + C d) - (C c * X + C d) ^ r - C d * (X ^ (r - 1) - 1) with hG
  have hker : G ∈ RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span {π}))) := by
    rw [RingHom.mem_ker, Polynomial.coe_mapRingHom, hG]
    exact map_frob2_eq_zero hdvr π hπ hres a e c d ha he
  rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hker
  obtain ⟨S, hS⟩ := Ideal.mem_span_singleton'.mp hker
  have h1 : aeval ζ G = algebraMap 𝒪 A π * aeval ζ S := by
    rw [← hS, map_mul, Polynomial.aeval_C, mul_comm]
  rw [hG] at h1
  simp only [map_sub, map_mul, map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_one] at h1
  have h2 := sub_eq_iff_eq_add'.mp h1
  rw [h2]
  exact isUnit_add_of_isNilpotent (((isUnit_of_not_mem_span hdvr π hπ d hd).map (algebraMap 𝒪 A)).mul hζ)
    (Commute.isNilpotent_mul_right (Commute.all _ _) hA)

omit [IsDomain 𝒪] in

theorem isUnit_pow_sub_one_of_mul_eq {A : Type} [CommRing A] (z D N : A) (hz : z * D = N)
    (hF : IsUnit (N ^ (r - 1) * D - D ^ r)) : IsUnit (z ^ (r - 1) - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, (Nat.sub_add_cancel (Fact.out : r.Prime).one_lt.le).symm⟩
  have hk' : r - 1 = k := by omega
  rw [hk'] at hF ⊢
  rw [hk] at hF
  have e : (z ^ k - 1) * D ^ (k + 1) = N ^ k * D - D ^ (k + 1) := by rw [← hz]; ring
  exact isUnit_of_mul_isUnit_left (e ▸ hF)

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem det_not_mem (M : GL (Fin 2) 𝒪) (I : Ideal 𝒪) (hI : I ≠ ⊤) (h01 : (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 ∈ I) :
    (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 ∉ I ∧ (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 ∉ I := by
  have hdet : IsUnit ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have key : (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 ∉ I := by
    intro hmem
    apply hI
    exact Ideal.eq_top_of_isUnit_mem _ (by simpa using I.sub_mem hmem h01) hdet
  exact ⟨fun h => key (I.mul_mem_right _ h), fun h => key (I.mul_mem_left _ h)⟩

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem det_not_mem' (M : GL (Fin 2) 𝒪) (I : Ideal 𝒪) (hI : I ≠ ⊤) (h00 : (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 ∈ I) :
    (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 ∉ I ∧ (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 ∉ I := by
  have hdet : IsUnit ((M : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have key : (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 * (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 ∉ I := by
    intro hmem
    apply hI
    exact Ideal.eq_top_of_isUnit_mem _ (by simpa using I.sub_mem h00 hmem) hdet
  exact ⟨fun h => key (I.mul_mem_right _ h), fun h => key (I.mul_mem_left _ h)⟩

end Units

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem tmul_comb {M : Type} [AddCommGroup M] [Module 𝒪 M] (u v : B) (a b c d : 𝒪) (x y : M) :
    u ⊗ₜ[𝒪] (a • x + c • y) + v ⊗ₜ[𝒪] (b • x + d • y) =
      (algebraMap 𝒪 B a * u + algebraMap 𝒪 B b * v) ⊗ₜ[𝒪] x + (algebraMap 𝒪 B c * u + algebraMap 𝒪 B d * v) ⊗ₜ[𝒪] y := by
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.add_tmul,
    Algebra.smul_def]
  abel

theorem col_identity (γ δ δ' : GL (Fin 2) K) (s : Kˣ) (m : Matrix (Fin 2) (Fin 2) 𝒪)
    (h : (γ : Matrix (Fin 2) (Fin 2) K) * (δ : Matrix (Fin 2) (Fin 2) K) * m.map (algebraMap 𝒪 K) =
      ((scalarGL s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (δ' : Matrix (Fin 2) (Fin 2) K))
    (q₀ q₁ : Fin 2 → K) (hq₀ : q₀ = (δ : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1))
    (hq₁ : q₁ = (δ : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 1 1))
    (p : Fin 2 → (Fin 2 → K)) (hp : ∀ j, p j = (δ' : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single j 1)) (j : Fin 2) :
    (s : K) • p j =
      m 0 j • (γ : Matrix (Fin 2) (Fin 2) K).mulVec q₀ + m 1 j • (γ : Matrix (Fin 2) (Fin 2) K).mulVec q₁ := by
  rw [hp j, hq₀, hq₁]
  have e : (s : K) • ((δ' : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single j 1)) =
      ((γ : Matrix (Fin 2) (Fin 2) K) * (δ : Matrix (Fin 2) (Fin 2) K) * m.map (algebraMap 𝒪 K)).mulVec (Pi.single j 1) := by
    rw [h, ← Matrix.mulVec_mulVec, scalarGL_mulVec]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_single_one,
    show (fun i => m.map (algebraMap 𝒪 K) i j) =
      algebraMap 𝒪 K (m 0 j) • (Pi.single 0 1 : Fin 2 → K) + algebraMap 𝒪 K (m 1 j) • (Pi.single 1 1 : Fin 2 → K) from by
        ext i; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Algebra.smul_def],
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    algebraMap_smul, algebraMap_smul]

theorem line_pullback_eq (π : 𝒪) (d : DeligneDatum (K := K) π B) (γ : GL (Fin 2) K) (Λ Λ' : FullLattice 𝒪 K) (s : Kˣ)
    (hrel : (FullLattice.act (scalarGL s) Λ').1 = (FullLattice.act γ Λ).1)
    (p₀ p₁ : ↥Λ.1) (p'₀ p'₁ : ↥Λ'.1) (m : Matrix (Fin 2) (Fin 2) 𝒪)
    (hcol : ∀ j : Fin 2, (s : K) • ((![p'₀, p'₁] j : ↥Λ'.1) : Fin 2 → K) =
      m 0 j • (γ : Matrix (Fin 2) (Fin 2) K).mulVec (p₀ : Fin 2 → K) +
      m 1 j • (γ : Matrix (Fin 2) (Fin 2) K).mulVec (p₁ : Fin 2 → K))
    (u v : B) (hline : d.line Λ' = Submodule.span B {u ⊗ₜ[𝒪] p'₀ + v ⊗ₜ[𝒪] p'₁}) :
    (DeligneDatum.pullback π B γ d).line Λ =
      Submodule.span B {(algebraMap 𝒪 B (m 0 0) * u + algebraMap 𝒪 B (m 0 1) * v) ⊗ₜ[𝒪] p₀ +
        (algebraMap 𝒪 B (m 1 0) * u + algebraMap 𝒪 B (m 1 1) * v) ⊗ₜ[𝒪] p₁} := by
  show (d.line (FullLattice.act γ Λ)).comap (actBaseChange B γ Λ).toLinearMap = _
  rw [DeligneDatum.line_transport π d hrel, d.homothety s Λ', hline, Submodule.map_span, Set.image_singleton,
    Submodule.map_span, Set.image_singleton, Submodule.comap_equiv_eq_map_symm, Submodule.map_span, Set.image_singleton]
  congr 2
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, map_add, map_add,
    actBaseChange_tmul, actBaseChange_tmul, map_add, actBaseChange_tmul, actBaseChange_tmul]
  have key : ∀ j : Fin 2, (LinearEquiv.ofEq _ _ hrel (latticeMapEquiv (scalarGL s) Λ'.1 (![p'₀, p'₁] j)) :
      ↥(FullLattice.act γ Λ).1) =
      ((m 0 j • latticeMapEquiv γ Λ.1 p₀ + m 1 j • latticeMapEquiv γ Λ.1 p₁ : ↥(FullLattice.act γ Λ).1)) := by
    intro j
    apply Subtype.ext
    rw [coe_ofEq_apply, coe_latticeMapEquiv_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, scalarGL_mulVec]
    exact hcol j
  have k0 := key 0
  have k1 := key 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at k0 k1
  erw [transportEquiv_tmul, transportEquiv_tmul, k0, k1]
  exact tmul_comb u v _ _ _ _ _ _

end Transport

section Lattices

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

theorem mem_act_g₁_iff (v : Fin 2 → K) :
    v ∈ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 ↔
      (∃ a : 𝒪, v 0 = algebraMap 𝒪 K (π * a)) ∧ IsLocalization.IsInteger 𝒪 (v 1) := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
    obtain ⟨a, ha⟩ := hw 0
    refine ⟨⟨a, ?_⟩, ?_⟩
    · rw [g₁_mulVec π g₁ hg₁]; simp [← ha, map_mul]
    · rw [g₁_mulVec π g₁ hg₁]; simpa using hw 1
  · rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    refine mem_latticeMap.mpr ⟨![algebraMap 𝒪 K a, algebraMap 𝒪 K c], ?_, ?_⟩
    · intro i; fin_cases i; exacts [⟨a, rfl⟩, ⟨c, rfl⟩]
    · rw [g₁_mulVec π g₁ hg₁]
      ext i; fin_cases i
      · simp [ha, map_mul]
      · simp [hc]

include hg₁ in

theorem act_g₁_le : (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 := by
  intro v hv
  obtain ⟨⟨a, ha⟩, h1⟩ := (mem_act_g₁_iff π g₁ hg₁ v).mp hv
  intro i; fin_cases i
  · exact ⟨π * a, ha.symm⟩
  · exact h1

include hg₁ in

theorem act_pi_le_act_g₁ :
    (FullLattice.act (scalarGL (unitK K π hπ0)) (stdFullLattice (𝒪 := 𝒪) K)).1 ≤
      (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  rw [scalarGL_mulVec, unitK_coe]
  refine (mem_act_g₁_iff π g₁ hg₁ _).mpr ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hw 0
    exact ⟨a, by rw [Pi.smul_apply, smul_eq_mul, ← ha, map_mul]⟩
  · rw [Pi.smul_apply, smul_eq_mul]
    exact IsLocalization.isInteger_mul ⟨π, rfl⟩ (hw 1)

omit [IsDomain 𝒪] [IsFractionRing 𝒪 K] in

theorem homothetic_of_vertex_act_eq (g : GL (Fin 2) K) {L L' : Submodule 𝒪 (Fin 2 → K)} {hL : IsFullLattice L}
    {hL' : IsFullLattice L'} (h : Vertex.act g (Vertex.mk 𝒪 K L hL) = Vertex.mk 𝒪 K L' hL') :
    ∃ c : Kˣ, latticeMap (scalarGL c) (latticeMap g L) = L' := by
  rw [Vertex.act_mk, Vertex.mk_eq_mk_iff] at h
  exact h

omit [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem latticeMap_scalarGL_comm (c : Kˣ) (g : GL (Fin 2) K) (L : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap g L) = latticeMap g (latticeMap (scalarGL c) L) := by
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]

include hπ0 hg₁ in

theorem latticeMap_act_g₁_eq_of_homothetic (h : GL (Fin 2) K) (hh : latticeMap h (stdLattice 𝒪 K) = stdLattice 𝒪 K)
    (hhom : Homothetic (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1)
      (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) :
    latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 = (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  set M₁ := (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 with hM₁
  obtain ⟨μ, hμ⟩ := hhom
  have hL : latticeMap h M₁ = latticeMap (scalarGL μ⁻¹) M₁ := by
    calc latticeMap h M₁ = latticeMap (scalarGL μ⁻¹) (latticeMap (scalarGL μ) (latticeMap h M₁)) := by
          rw [← latticeMap_mul (scalarGL μ⁻¹), ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
      _ = latticeMap (scalarGL μ⁻¹) M₁ := by rw [hμ]
  have h1 : latticeMap (scalarGL μ⁻¹) M₁ ≤ stdLattice 𝒪 K := by
    rw [← hL]
    exact (latticeMap_mono h (act_g₁_le π g₁ hg₁)).trans hh.le
  have h2 : latticeMap (scalarGL (unitK K π hπ0)) (stdLattice 𝒪 K) ≤ latticeMap (scalarGL μ⁻¹) M₁ := by
    rw [← hL]
    have := latticeMap_mono h (act_pi_le_act_g₁ π hπ0 g₁ hg₁)
    change latticeMap h (latticeMap (scalarGL (unitK K π hπ0)) (stdLattice 𝒪 K)) ≤ latticeMap h M₁ at this
    rwa [← latticeMap_scalarGL_comm, hh] at this

  have he1 : (Pi.single 1 1 : Fin 2 → K) ∈ M₁ :=
    (mem_act_g₁_iff π g₁ hg₁ _).mpr ⟨⟨0, by simp⟩, by simpa using IsLocalization.isInteger_one (R := 𝒪)⟩
  obtain ⟨t, ht⟩ : IsLocalization.IsInteger 𝒪 ((μ⁻¹ : Kˣ) : K) := by
    have hm : ((μ⁻¹ : Kˣ) : K) • (Pi.single 1 1 : Fin 2 → K) ∈ latticeMap (scalarGL μ⁻¹) M₁ :=
      mem_latticeMap_scalarGL.mpr ⟨_, he1, rfl⟩
    have := h1 hm 1
    simpa using this

  have hπe0 : ((unitK K π hπ0 : Kˣ) : K) • (Pi.single 0 1 : Fin 2 → K) ∈ latticeMap (scalarGL μ⁻¹) M₁ :=
    h2 (mem_latticeMap_scalarGL.mpr ⟨_, single_one_mem_stdLattice 𝒪 K 0, rfl⟩)
  obtain ⟨w, hw, hw'⟩ := mem_latticeMap_scalarGL.mp hπe0
  obtain ⟨⟨a, ha⟩, -⟩ := (mem_act_g₁_iff π g₁ hg₁ w).mp hw
  have hta : t * a = 1 := by
    have e := congrFun hw' 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, unitK_coe] at e
    rw [ha, ← ht, ← map_mul] at e
    have e2 : t * (π * a) = π := IsFractionRing.injective 𝒪 K e
    have e3 : π * (t * a) = π * 1 := by rw [mul_one]; linear_combination e2
    exact mul_left_cancel₀ hπ0 e3
  rw [hL]
  exact latticeMap_scalarGL_eq_self_of_isUnit (isUnit_iff_exists_inv.mpr ⟨a, hta⟩) ht.symm M₁

include hπ0 hg₁ in

theorem latticeMap_act_g₁_eq_of_homothetic' (h : GL (Fin 2) K)
    (hh : latticeMap h (stdLattice 𝒪 K) = (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1)
    (hhom : Homothetic (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) (stdLattice 𝒪 K)) :
    latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 = latticeMap (scalarGL (unitK K π hπ0)) (stdLattice 𝒪 K) := by
  set M₁ := (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 with hM₁
  obtain ⟨μ, hμ⟩ := hhom
  have hL : latticeMap h M₁ = latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) := by
    calc latticeMap h M₁ = latticeMap (scalarGL μ⁻¹) (latticeMap (scalarGL μ) (latticeMap h M₁)) := by
          rw [← latticeMap_mul (scalarGL μ⁻¹), ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
      _ = latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) := by rw [hμ]
  have h1 : latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) ≤ M₁ := by
    rw [← hL]
    exact (latticeMap_mono h (act_g₁_le π g₁ hg₁)).trans hh.le
  have h2 : latticeMap (scalarGL (unitK K π hπ0)) M₁ ≤ latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) := by
    rw [← hL]
    have := latticeMap_mono h (act_pi_le_act_g₁ π hπ0 g₁ hg₁)
    change latticeMap h (latticeMap (scalarGL (unitK K π hπ0)) (stdLattice 𝒪 K)) ≤ latticeMap h M₁ at this
    rwa [← latticeMap_scalarGL_comm, hh] at this

  have hm0 : ((μ⁻¹ : Kˣ) : K) • (Pi.single 0 1 : Fin 2 → K) ∈ latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) :=
    mem_latticeMap_scalarGL.mpr ⟨_, single_one_mem_stdLattice 𝒪 K 0, rfl⟩
  obtain ⟨⟨a, ha⟩, -⟩ := (mem_act_g₁_iff π g₁ hg₁ _).mp (h1 hm0)
  rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at ha

  have he1 : (Pi.single 1 1 : Fin 2 → K) ∈ M₁ :=
    (mem_act_g₁_iff π g₁ hg₁ _).mpr ⟨⟨0, by simp⟩, by simpa using IsLocalization.isInteger_one (R := 𝒪)⟩
  have hπe1 : ((unitK K π hπ0 : Kˣ) : K) • (Pi.single 1 1 : Fin 2 → K) ∈ latticeMap (scalarGL μ⁻¹) (stdLattice 𝒪 K) :=
    h2 (mem_latticeMap_scalarGL.mpr ⟨_, he1, rfl⟩)
  obtain ⟨w, hw, hw'⟩ := mem_latticeMap_scalarGL.mp hπe1
  obtain ⟨b, hb⟩ := hw 1
  have hab : a * b = 1 := by
    have e := congrFun hw' 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, unitK_coe] at e
    rw [ha, ← hb, ← map_mul] at e
    have e2 : π * a * b = π := IsFractionRing.injective 𝒪 K e
    have e3 : π * (a * b) = π * 1 := by rw [mul_one]; linear_combination e2
    exact mul_left_cancel₀ hπ0 e3
  have hau : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, hab⟩
  rw [hL, show scalarGL μ⁻¹ = scalarGL (unitK K π hπ0) * scalarGL ((unitK K π hπ0)⁻¹ * μ⁻¹) by
    rw [← scalarGL_mul, mul_inv_cancel_left], latticeMap_mul,
    latticeMap_scalarGL_eq_self_of_isUnit hau _ (stdLattice 𝒪 K)]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, unitK_coe, ha, map_mul, ← mul_assoc,
    inv_mul_cancel₀ ((unitK_coe (K := K) π hπ0) ▸ (unitK K π hπ0).ne_zero), one_mul]

end Lattices

section Cases

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable (π : 𝒪) (hπ0 : π ≠ 0)
variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])

omit [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem coe_map (m : GL (Fin 2) 𝒪) :
    ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (m : Matrix (Fin 2) (Fin 2) 𝒪).map (algebraMap 𝒪 K) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply _ i j m

omit [IsDomain 𝒪] in
theorem exists_map_eq (h : GL (Fin 2) K) (hh : latticeMap h (stdLattice 𝒪 K) = stdLattice 𝒪 K) :
    ∃ m : GL (Fin 2) 𝒪, Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m = h :=
  MonoidHom.mem_range.mp ((latticeMap_stdLattice_eq_iff_mem_range h).mp hh)

include hπ0 hg₁ in

theorem entries_of_conj (m m' : Matrix (Fin 2) (Fin 2) 𝒪)
    (h : (g₁ : Matrix (Fin 2) (Fin 2) K) * m'.map (algebraMap 𝒪 K) = m.map (algebraMap 𝒪 K) * (g₁ : Matrix (Fin 2) (Fin 2) K)) :
    m' 0 0 = m 0 0 ∧ π * m' 0 1 = m 0 1 ∧ m' 1 0 = m 1 0 * π ∧ m' 1 1 = m 1 1 := by
  have hinj := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun e => hπ0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp e)
  rw [hg₁] at h
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, one_mul, mul_one] at e00 e01 e10 e11
  refine ⟨hinj (mul_left_cancel₀ hπK (e00.trans (mul_comm _ _))), hinj ?_, hinj ?_, hinj e11⟩
  · rw [map_mul]; exact e01
  · rw [map_mul]; exact e10

include hπ0 hg₁ in

theorem entries_of_conj' (m m' : Matrix (Fin 2) (Fin 2) 𝒪)
    (h : algebraMap 𝒪 K π • m.map (algebraMap 𝒪 K) =
      (g₁ : Matrix (Fin 2) (Fin 2) K) * m'.map (algebraMap 𝒪 K) * (g₁ : Matrix (Fin 2) (Fin 2) K)) :
    m 0 0 = m' 0 0 * π ∧ m 0 1 = m' 0 1 ∧ m 1 0 = m' 1 0 ∧ π * m 1 1 = m' 1 1 := by
  have hinj := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun e => hπ0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp e)
  rw [hg₁] at h
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp only [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, one_mul, mul_one, smul_eq_mul] at e00 e01 e10 e11
  refine ⟨hinj (mul_left_cancel₀ hπK ?_), hinj (mul_left_cancel₀ hπK e01), hinj (mul_left_cancel₀ hπK ?_), hinj ?_⟩
  · rw [e00, map_mul]; ring
  · rw [e10, mul_comm]
  · rw [map_mul]; exact e11

include hπ0 hg₁ in

theorem caseA (g : GL (Fin 2) K)
    (hA : Vertex.act g (stdVertex 𝒪 K) = stdVertex 𝒪 K ∧
      Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = Vertex.act g₁ (stdVertex 𝒪 K)) :
    ∃ (c : Kˣ) (m m' : GL (Fin 2) 𝒪),
      (FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K)).1 = (FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1 ∧
      (FullLattice.act (scalarGL c) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K))).1 =
        (FullLattice.act g⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K))).1 ∧
      g⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m = scalarGL c ∧
      g⁻¹ * g₁ * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m' = scalarGL c * g₁ ∧
      ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 = (m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 ∧
        π * (m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 = (m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 ∧
        (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 = (m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 * π ∧
        (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 = (m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) := by
  have hA1 : Vertex.act g (Vertex.mk 𝒪 K (stdLattice 𝒪 K) isFullLattice_stdLattice) =
      Vertex.mk 𝒪 K (stdLattice 𝒪 K) isFullLattice_stdLattice := hA.1
  obtain ⟨c, hc⟩ := homothetic_of_vertex_act_eq g hA1
  have hA2 : Vertex.act g (Vertex.mk 𝒪 K (latticeMap g₁ (stdLattice 𝒪 K)) (isFullLattice_stdLattice.map g₁)) =
      Vertex.mk 𝒪 K (latticeMap g₁ (stdLattice 𝒪 K)) (isFullLattice_stdLattice.map g₁) := hA.2
  obtain ⟨c₂, hc₂⟩ := homothetic_of_vertex_act_eq g hA2
  set h : GL (Fin 2) K := scalarGL c * g with hh_def
  have hh : latticeMap h (stdLattice 𝒪 K) = stdLattice 𝒪 K := by rw [hh_def, latticeMap_mul]; exact hc
  have hhom : Homothetic (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1)
      (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    refine ⟨c₂ * c⁻¹, ?_⟩
    show latticeMap (scalarGL (c₂ * c⁻¹)) (latticeMap (scalarGL c * g) (latticeMap g₁ (stdLattice 𝒪 K))) =
      latticeMap g₁ (stdLattice 𝒪 K)
    rw [← latticeMap_mul, ← mul_assoc, ← scalarGL_mul, inv_mul_cancel_right, latticeMap_mul]
    exact hc₂
  have hh1 := latticeMap_act_g₁_eq_of_homothetic π hπ0 g₁ hg₁ h hh hhom
  obtain ⟨m, hm⟩ := exists_map_eq (𝒪 := 𝒪) (K := K) h hh
  obtain ⟨m', hm'⟩ := exists_map_eq (𝒪 := 𝒪) (K := K) (g₁⁻¹ * h * g₁) (by
    rw [latticeMap_mul, latticeMap_mul]
    change latticeMap g₁⁻¹ (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) = stdLattice 𝒪 K
    rw [hh1]
    exact latticeMap_inv_latticeMap g₁ (stdLattice 𝒪 K))
  have hgh : g⁻¹ * h = scalarGL c := by
    rw [hh_def, scalarGL_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨c, m, m', ?_, ?_, ?_, ?_, ?_⟩
  · show latticeMap (scalarGL c) (stdLattice 𝒪 K) = latticeMap g⁻¹ (stdLattice 𝒪 K)
    conv_rhs => rw [← hh, ← latticeMap_mul, hgh]
  · show latticeMap (scalarGL c) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 =
      latticeMap g⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1
    conv_rhs => rw [← hh1, ← latticeMap_mul, hgh]
  · rw [hm, hgh]
  · rw [hm', hh_def, scalarGL_mul_comm]; group
  · apply entries_of_conj π hπ0 g₁ hg₁
    rw [← coe_map, ← coe_map, ← Units.val_mul, ← Units.val_mul, hm, hm', ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

include hπ0 hg₁ in

theorem caseB (g : GL (Fin 2) K)
    (hB : Vertex.act g (stdVertex 𝒪 K) = Vertex.act g₁ (stdVertex 𝒪 K) ∧
      Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = stdVertex 𝒪 K) :
    ∃ (c : Kˣ) (m m' : GL (Fin 2) 𝒪),
      (FullLattice.act (scalarGL (c * (unitK K π hπ0)⁻¹)) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K))).1 =
        (FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1 ∧
      (FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K)).1 =
        (FullLattice.act g⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K))).1 ∧
      g⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m = scalarGL (c * (unitK K π hπ0)⁻¹) * g₁ ∧
      g⁻¹ * g₁ * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m' = scalarGL c ∧
      ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 = (m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 * π ∧
        (m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 = (m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 ∧
        (m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 = (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 ∧
        π * (m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 = (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) := by
  have hB1 : Vertex.act g (Vertex.mk 𝒪 K (stdLattice 𝒪 K) isFullLattice_stdLattice) =
      Vertex.mk 𝒪 K (latticeMap g₁ (stdLattice 𝒪 K)) (isFullLattice_stdLattice.map g₁) := hB.1
  have hB2 : Vertex.act g (Vertex.mk 𝒪 K (latticeMap g₁ (stdLattice 𝒪 K)) (isFullLattice_stdLattice.map g₁)) =
      Vertex.mk 𝒪 K (stdLattice 𝒪 K) isFullLattice_stdLattice := hB.2
  obtain ⟨c, hc⟩ := homothetic_of_vertex_act_eq g hB1
  obtain ⟨c₂, hc₂⟩ := homothetic_of_vertex_act_eq g hB2
  set h : GL (Fin 2) K := scalarGL c * g with hh_def
  set ϖ : Kˣ := unitK K π hπ0 with hϖ
  have hh : latticeMap h (stdLattice 𝒪 K) = (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    rw [hh_def, latticeMap_mul]; exact hc
  have hhom : Homothetic (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) (stdLattice 𝒪 K) := by
    refine ⟨c₂ * c⁻¹, ?_⟩
    show latticeMap (scalarGL (c₂ * c⁻¹)) (latticeMap (scalarGL c * g) (latticeMap g₁ (stdLattice 𝒪 K))) = stdLattice 𝒪 K
    rw [← latticeMap_mul, ← mul_assoc, ← scalarGL_mul, inv_mul_cancel_right, latticeMap_mul]
    exact hc₂
  have hh1 := latticeMap_act_g₁_eq_of_homothetic' π hπ0 g₁ hg₁ h hh hhom
  obtain ⟨m, hm⟩ := exists_map_eq (𝒪 := 𝒪) (K := K) ((scalarGL ϖ)⁻¹ * h * g₁) (by
    rw [latticeMap_mul, latticeMap_mul]
    change latticeMap (scalarGL ϖ)⁻¹ (latticeMap h (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) = stdLattice 𝒪 K
    rw [hh1, latticeMap_inv_latticeMap])
  obtain ⟨m', hm'⟩ := exists_map_eq (𝒪 := 𝒪) (K := K) (g₁⁻¹ * h) (by
    rw [latticeMap_mul, hh]
    exact latticeMap_inv_latticeMap g₁ (stdLattice 𝒪 K))
  have hgh : g⁻¹ * h = scalarGL c := by
    rw [hh_def, scalarGL_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hscal : scalarGL (c * ϖ⁻¹) = (scalarGL ϖ)⁻¹ * scalarGL c := by
    rw [scalarGL_mul, scalarGL_mul_comm, show scalarGL ϖ⁻¹ = (scalarGL ϖ)⁻¹ from
      (inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])).symm]
  have hcomm : g⁻¹ * (scalarGL ϖ)⁻¹ = (scalarGL ϖ)⁻¹ * g⁻¹ :=
    ((show Commute (scalarGL ϖ) g from scalarGL_mul_comm ϖ g).inv_inv).eq.symm
  refine ⟨c, m, m', ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : stdLattice 𝒪 K = latticeMap ((scalarGL ϖ)⁻¹ * h) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
      rw [latticeMap_mul, hh1, latticeMap_inv_latticeMap]
    show latticeMap (scalarGL (c * ϖ⁻¹)) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1 = latticeMap g⁻¹ (stdLattice 𝒪 K)
    rw [hscal, e1, ← latticeMap_mul, ← hgh]
    conv_rhs => rw [← mul_assoc, hcomm]
    rw [← mul_assoc]
  · show latticeMap (scalarGL c) (stdLattice 𝒪 K) = latticeMap g⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1
    rw [← hh, ← latticeMap_mul, hgh]
  · rw [hm, hscal, ← hgh]
    calc g⁻¹ * ((scalarGL ϖ)⁻¹ * h * g₁) = (g⁻¹ * (scalarGL ϖ)⁻¹) * h * g₁ := by group
      _ = ((scalarGL ϖ)⁻¹ * g⁻¹) * h * g₁ := by rw [hcomm]
      _ = (scalarGL ϖ)⁻¹ * (g⁻¹ * h) * g₁ := by group
  · rw [hm', ← hgh]; group
  · apply entries_of_conj' π hπ0 g₁ hg₁
    have e : (scalarGL ϖ : GL (Fin 2) K) * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m =
        g₁ * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) m' * g₁ := by
      rw [hm, hm']; group
    have e' := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) e
    simp only [Units.val_mul, coe_map, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul] at e'
    rw [← unitK_coe (K := K) π hπ0]
    exact e'

end Cases

section EdgeRing

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

abbrev An (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ) : Type :=
  (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})

abbrev xiA (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ) : An 𝒪 π r n :=
  Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.ξ 𝒪 π r)

abbrev etaA (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ) : An 𝒪 π r n :=
  Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.η 𝒪 π r)

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem isNilpotent_An (π : 𝒪) (n : ℕ) : IsNilpotent (algebraMap 𝒪 (An 𝒪 π r n) π) :=
  isNilpotent_algebraMap_modPow π (chartERing 𝒪 π r) n

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem algebraMap_pow_eq_zero_An (π : 𝒪) (n : ℕ) : algebraMap 𝒪 (An 𝒪 π r n) π ^ (n + 1) = 0 := by
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (chartERing 𝒪 π r) (An 𝒪 π r n), Ideal.Quotient.algebraMap_eq, map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem xi_mul_eta (π : 𝒪) (n : ℕ) : xiA 𝒪 π r n * etaA 𝒪 π r n = algebraMap 𝒪 (An 𝒪 π r n) π := by
  rw [← map_mul, chartERing.ξ_mul_η, IsScalarTower.algebraMap_apply 𝒪 (chartERing 𝒪 π r) (An 𝒪 π r n),
    Ideal.Quotient.algebraMap_eq]

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem isUnit_xi_eta (π : 𝒪) (n : ℕ) : IsUnit (xiA 𝒪 π r n ^ (r - 1) - 1) ∧ IsUnit (etaA 𝒪 π r n ^ (r - 1) - 1) := by
  have h := (chartERing.isUnit_discr 𝒪 π r).map (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))
  rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one] at h
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem point_facts (π : 𝒪) (n : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) :
    IsNilpotent (algebraMap 𝒪 B π) ∧ x (xiA 𝒪 π r n) * x (etaA 𝒪 π r n) = algebraMap 𝒪 B π ∧
      IsUnit (x (xiA 𝒪 π r n) ^ (r - 1) - 1) ∧ IsUnit (x (etaA 𝒪 π r n) ^ (r - 1) - 1) := by
  obtain ⟨h1, h2⟩ := isUnit_xi_eta (r := r) π n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← x.commutes π]; exact (isNilpotent_An π n).map x
  · rw [← map_mul, xi_mul_eta, AlgHom.commutes]
  · have h := h1.map x; rwa [map_sub, map_pow, map_one] at h
  · have h := h2.map x; rwa [map_sub, map_pow, map_one] at h

omit [Fact r.Prime] [IsDomain 𝒪] in

theorem algHom_ext_An (π : 𝒪) (n : ℕ) {C : Type} [CommRing C] [Algebra 𝒪 C] (f g : An 𝒪 π r n →ₐ[𝒪] C)
    (hξ : f (xiA 𝒪 π r n) = g (xiA 𝒪 π r n)) (hη : f (etaA 𝒪 π r n) = g (etaA 𝒪 π r n)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (Submonoid.powers (edgeQuot.discr 𝒪 π r))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hξ
  · exact hη

omit [Fact r.Prime] [IsDomain 𝒪] in

def liftE (π : 𝒪) (n : ℕ) (p : (chartE 𝒪 π r).obj (An 𝒪 π r n)) : An 𝒪 π r n →ₐ[𝒪] An 𝒪 π r n :=
  Ideal.Quotient.liftₐ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.lift p) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, AlgHom.commutes, algebraMap_pow_eq_zero_An, mul_zero])

omit [Fact r.Prime] [IsDomain 𝒪] in
@[scoped simp] theorem liftE_xi (π : 𝒪) (n : ℕ) (p : (chartE 𝒪 π r).obj (An 𝒪 π r n)) : liftE π n p (xiA 𝒪 π r n) = p.1.1 := by
  show Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact chartERing.lift_ξ _

omit [Fact r.Prime] [IsDomain 𝒪] in
@[scoped simp] theorem liftE_eta (π : 𝒪) (n : ℕ) (p : (chartE 𝒪 π r).obj (An 𝒪 π r n)) : liftE π n p (etaA 𝒪 π r n) = p.1.2 := by
  show Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact chartERing.lift_η _

variable (π : 𝒪) (g₁ : GL (Fin 2) K) (n : ℕ)

abbrev IsECH {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (x : An 𝒪 π r n →ₐ[𝒪] B) : Prop :=
  d.line (stdFullLattice K) =
      Submodule.span B {((x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
        (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
    d.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 +
        ((x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
          (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K 1}).map (actBaseChange B g₁ (stdFullLattice K)).toLinearMap ∧
    d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K)

variable {π g₁ n} in
omit [Fact r.Prime] [IsDomain 𝒪] in

theorem point_eq_of_isECH {B : Type} [CommRing B] [Algebra 𝒪 B] {d : DeligneDatum (K := K) π B}
    {x x' : An 𝒪 π r n →ₐ[𝒪] B} (h : IsECH π g₁ n d x) (h' : IsECH π g₁ n d x') :
    x (xiA 𝒪 π r n) = x' (xiA 𝒪 π r n) ∧ x (etaA 𝒪 π r n) = x' (etaA 𝒪 π r n) :=
  ⟨eq_of_span_tmul_add_one_tmul_eq B _ _ (h.1.symm.trans h'.1),
    eq_of_map_span_one_tmul_add_tmul_eq B g₁ _ _ (h.2.1.symm.trans h'.2.1)⟩

theorem exists_isECH (hdvr : IsDiscreteValuationRing 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) :
    ∃ d : DeligneDatum (K := K) π B, IsECH π g₁ n d x := by
  haveI := hdvr
  exact CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K) π hπ r hres g₁ hg₁ B
    (point_facts π n x).1 _

def TP (g : GL (Fin 2) K) (ξ' η' : An 𝒪 π r n) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d : DeligneDatum (K := K) π B),
    IsECH π g₁ n d x →
      (DeligneDatum.pullback π B g⁻¹ d).line (stdFullLattice K) =
          Submodule.span B {x ξ' ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
        (DeligneDatum.pullback π B g⁻¹ d).line (FullLattice.act g₁ (stdFullLattice K)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + x η' ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange B g₁ (stdFullLattice K)).toLinearMap

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in

theorem span_pair_eq {B : Type} [CommRing B] [Algebra 𝒪 B] {M : Type} [AddCommGroup M] [Module 𝒪 M] (p₀ p₁ : M)
    (N D z : B) (hD : IsUnit D) (hz : z * D = N) :
    Submodule.span B {N ⊗ₜ[𝒪] p₀ + D ⊗ₜ[𝒪] p₁} = Submodule.span B {z ⊗ₜ[𝒪] p₀ + (1 : B) ⊗ₜ[𝒪] p₁} := by
  rw [← Submodule.span_singleton_smul_eq hD (z ⊗ₜ[𝒪] p₀ + (1 : B) ⊗ₜ[𝒪] p₁), smul_add, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_comm D z, hz]

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in

theorem span_pair_eq' {B : Type} [CommRing B] [Algebra 𝒪 B] {M : Type} [AddCommGroup M] [Module 𝒪 M] (p₀ p₁ : M)
    (N D z : B) (hN : IsUnit N) (hz : z * N = D) :
    Submodule.span B {N ⊗ₜ[𝒪] p₀ + D ⊗ₜ[𝒪] p₁} = Submodule.span B {(1 : B) ⊗ₜ[𝒪] p₀ + z ⊗ₜ[𝒪] p₁} := by
  rw [← Submodule.span_singleton_smul_eq hN ((1 : B) ⊗ₜ[𝒪] p₀ + z ⊗ₜ[𝒪] p₁), smul_add, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_comm N z, hz]

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in

theorem map_span_eq {B : Type} [CommRing B] [Algebra 𝒪 B] (u v : B) :
    (Submodule.span B {u ⊗ₜ[𝒪] stdBasisVec K 0 + v ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap =
      Submodule.span B {u ⊗ₜ[𝒪] latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) +
        v ⊗ₜ[𝒪] latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)} := by
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, map_add, actBaseChange_tmul, actBaseChange_tmul]
  rfl

end EdgeRing

section TransportPoint

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
variable (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (n : ℕ)

include hdvr hπ hres hg₁ in

theorem transportPoint_A (g : GL (Fin 2) K)
    (hA : Vertex.act g (stdVertex 𝒪 K) = stdVertex 𝒪 K ∧
      Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = Vertex.act g₁ (stdVertex 𝒪 K)) :
    ∃ ξ' η' : An 𝒪 π r n, ξ' * η' = algebraMap 𝒪 (An 𝒪 π r n) π ∧ IsUnit (ξ' ^ (r - 1) - 1) ∧ IsUnit (η' ^ (r - 1) - 1) ∧
      TP π g₁ n g ξ' η' ∧ Associated ξ' (xiA 𝒪 π r n) ∧ Associated η' (etaA 𝒪 π r n) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hI : Ideal.span {π} ≠ ⊤ := by rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit
  obtain ⟨c, m, m', hrel0, hrel1, hmat0, hmat1, e00, e01, e10, e11⟩ := caseA π hπ0 g₁ hg₁ g hA
  set ξ := xiA 𝒪 π r n with hξ
  set η := etaA 𝒪 π r n with hη
  obtain ⟨hAn, hξη, hξu, hηu⟩ := point_facts (r := r) π n (AlgHom.id 𝒪 (An 𝒪 π r n))
  change IsNilpotent (algebraMap 𝒪 (An 𝒪 π r n) π) at hAn
  change ξ * η = algebraMap 𝒪 (An 𝒪 π r n) π at hξη
  change IsUnit (ξ ^ (r - 1) - 1) at hξu
  change IsUnit (η ^ (r - 1) - 1) at hηu

  have h01 : (m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 ∈ Ideal.span {π} :=
    Ideal.mem_span_singleton'.mpr ⟨(m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1, by rw [mul_comm]; exact e01⟩
  have h'10 : (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0 ∈ Ideal.span {π} :=
    Ideal.mem_span_singleton'.mpr ⟨(m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0, e10.symm⟩
  obtain ⟨h00, h11⟩ := det_not_mem m _ hI (Ideal.mul_mem_right _ _ h01)
  obtain ⟨h'00, h'11⟩ := det_not_mem m' _ hI (Ideal.mul_mem_left _ _ h'10)

  set aA := algebraMap 𝒪 (An 𝒪 π r n) with haA
  set N : An 𝒪 π r n := aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * ξ + aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) with hN
  set D : An 𝒪 π r n := aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * ξ + aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) with hD
  set N' : An 𝒪 π r n := aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) * η + aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) with hN'
  set D' : An 𝒪 π r n := aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) * η + aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) with hD'
  have hDu : IsUnit D := isUnit_linear' hdvr π hπ hres hAn ξ hξu _ _ h11
  have hN'u : IsUnit N' := isUnit_linear' hdvr π hπ hres hAn η hηu _ _ h'00
  set ξ' : An 𝒪 π r n := N * ↑hDu.unit⁻¹ with hξ'
  set η' : An 𝒪 π r n := D' * ↑hN'u.unit⁻¹ with hη'
  have hξ'D : ξ' * D = N := by rw [hξ', mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hη'N : η' * N' = D' := by rw [hη', mul_assoc, IsUnit.val_inv_mul, mul_one]

  have r01 : aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) = ξ * η * aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) := by
    rw [hξη, ← map_mul, e01]
  have r'10 : aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) = aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * (ξ * η) := by
    rw [hξη, ← map_mul, e10]
  have r'00 : aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) = aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) := by rw [e00]
  have r'11 : aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) = aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) := by rw [e11]
  have rel : N * D' = ξ * η * (D * N') := by
    simp only [hN, hD, hN', hD', r01, r'10, r'00, r'11]; ring
  refine ⟨ξ', η', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hξη]
    have e : ξ' * η' * (D * N') = ξ * η * (D * N') := by
      rw [← rel, ← hξ'D, ← hη'N]; ring
    exact (hDu.mul hN'u).mul_left_injective e
  · exact isUnit_pow_sub_one_of_mul_eq (r := r) ξ' D N hξ'D (isUnit_frob2 hdvr π hπ hres hAn ξ hξu _ _ _ _ h00 h01 h11)
  · exact isUnit_pow_sub_one_of_mul_eq (r := r) η' N' D' hη'N (isUnit_frob2 hdvr π hπ hres hAn η hηu _ _ _ _ h'11 h'10 h'00)
  ·
    intro B _ _ x d hd
    obtain ⟨hB, hxξη, hxξu, hxηu⟩ := point_facts (r := r) π n x
    have hcol0 := col_identity (𝒪 := 𝒪) g⁻¹ 1 1 c (m : Matrix (Fin 2) (Fin 2) 𝒪) (by
      rw [Units.val_one, mul_one, mul_one, ← coe_map, ← Units.val_mul, hmat0])
      ((stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
      ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
      (by rw [Units.val_one, Matrix.one_mulVec]; rfl) (by rw [Units.val_one, Matrix.one_mulVec]; rfl)
      (fun j => ((![stdBasisVec (𝒪 := 𝒪) K 0, stdBasisVec (𝒪 := 𝒪) K 1] j : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K))
      (by intro j; fin_cases j <;> (rw [Units.val_one, Matrix.one_mulVec]; rfl))
    have hcol1 := col_identity (𝒪 := 𝒪) g⁻¹ g₁ g₁ c (m' : Matrix (Fin 2) (Fin 2) 𝒪) (by
      rw [← coe_map, ← Units.val_mul, ← Units.val_mul, hmat1, Units.val_mul])
      ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) : ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
      ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1) : ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
      rfl rfl
      (fun j => ((![latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0),
        latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)] j :
          ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K))
      (by intro j; fin_cases j <;> rfl)
    have t0 := line_pullback_eq π d g⁻¹ (stdFullLattice K) (stdFullLattice K) c hrel0 (stdBasisVec K 0) (stdBasisVec K 1)
      (stdBasisVec K 0) (stdBasisVec K 1) (m : Matrix (Fin 2) (Fin 2) 𝒪) hcol0 _ _ hd.1
    have t1 := line_pullback_eq π d g⁻¹ (FullLattice.act g₁ (stdFullLattice K)) (FullLattice.act g₁ (stdFullLattice K)) c hrel1
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0))
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1))
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0))
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)) (m' : Matrix (Fin 2) (Fin 2) 𝒪) hcol1 _ _
      ((hd.2.1.trans (map_span_eq g₁ _ _)))
    constructor
    · rw [t0]
      have e : (algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) +
            algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) * 1) = x N ∧
          (algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) +
            algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) * 1) = x D := by
        constructor <;> simp only [hN, hD, haA, map_add, map_mul, AlgHom.commutes, mul_one] <;> rfl
      rw [e.1, e.2]
      exact span_pair_eq _ _ _ _ _ (hDu.map x) (by rw [← map_mul, hξ'D])
    · rw [t1, map_span_eq]
      have e : (algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * 1 + algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) = x N' ∧
          (algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * 1 + algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) = x D' := by
        constructor <;> simp only [hN', hD', haA, map_add, map_mul, AlgHom.commutes, mul_one] <;>
          first | rfl | (rw [add_comm]; rfl)
      rw [e.1, e.2]
      exact span_pair_eq' _ _ _ _ _ (hN'u.map x) (by rw [← map_mul, hη'N])
  ·
    have hu : IsUnit (aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) * η + aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0)) :=
      isUnit_linear' hdvr π hπ hres hAn η hηu _ _ h00
    refine (Associated.symm ⟨hu.unit * hDu.unit⁻¹, ?_⟩)
    rw [Units.val_mul, hξ', ← mul_assoc]
    congr 1
    rw [IsUnit.unit_spec, hN, r01]; ring
  ·
    refine (Associated.symm ⟨hDu.unit * hN'u.unit⁻¹, ?_⟩)
    rw [Units.val_mul, hη', ← mul_assoc]
    congr 1
    rw [IsUnit.unit_spec, hD', hD, r'10, r'11]; ring

include hdvr hπ hres hg₁ in

theorem transportPoint_B (g : GL (Fin 2) K)
    (hB : Vertex.act g (stdVertex 𝒪 K) = Vertex.act g₁ (stdVertex 𝒪 K) ∧
      Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = stdVertex 𝒪 K) :
    ∃ ξ' η' : An 𝒪 π r n, ξ' * η' = algebraMap 𝒪 (An 𝒪 π r n) π ∧ IsUnit (ξ' ^ (r - 1) - 1) ∧ IsUnit (η' ^ (r - 1) - 1) ∧
      TP π g₁ n g ξ' η' ∧ Associated ξ' (etaA 𝒪 π r n) ∧ Associated η' (xiA 𝒪 π r n) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hI : Ideal.span {π} ≠ ⊤ := by rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit
  obtain ⟨c, m, m', hrel0, hrel1, hmat0, hmat1, e00, e01, e10, e11⟩ := caseB π hπ0 g₁ hg₁ g hB
  set ξ := xiA 𝒪 π r n with hξ
  set η := etaA 𝒪 π r n with hη
  obtain ⟨hAn, hξη, hξu, hηu⟩ := point_facts (r := r) π n (AlgHom.id 𝒪 (An 𝒪 π r n))
  change IsNilpotent (algebraMap 𝒪 (An 𝒪 π r n) π) at hAn
  change ξ * η = algebraMap 𝒪 (An 𝒪 π r n) π at hξη
  change IsUnit (ξ ^ (r - 1) - 1) at hξu
  change IsUnit (η ^ (r - 1) - 1) at hηu
  have h00 : (m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0 ∈ Ideal.span {π} :=
    Ideal.mem_span_singleton'.mpr ⟨(m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0, e00.symm⟩
  have h'11 : (m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 ∈ Ideal.span {π} :=
    Ideal.mem_span_singleton'.mpr ⟨(m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1, by rw [mul_comm]; exact e11⟩
  obtain ⟨h01, h10⟩ := det_not_mem' m _ hI (Ideal.mul_mem_right _ _ h00)
  obtain ⟨h'01, h'10⟩ := det_not_mem' m' _ hI (Ideal.mul_mem_left _ _ h'11)
  set aA := algebraMap 𝒪 (An 𝒪 π r n) with haA
  set N : An 𝒪 π r n := aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) * η + aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) with hN
  set D : An 𝒪 π r n := aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) * η + aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) with hD
  set N' : An 𝒪 π r n := aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * ξ + aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) with hN'
  set D' : An 𝒪 π r n := aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * ξ + aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) with hD'
  have hDu : IsUnit D := isUnit_linear' hdvr π hπ hres hAn η hηu _ _ h10
  have hN'u : IsUnit N' := isUnit_linear' hdvr π hπ hres hAn ξ hξu _ _ h'01
  set ξ' : An 𝒪 π r n := N * ↑hDu.unit⁻¹ with hξ'
  set η' : An 𝒪 π r n := D' * ↑hN'u.unit⁻¹ with hη'
  have hξ'D : ξ' * D = N := by rw [hξ', mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hη'N : η' * N' = D' := by rw [hη', mul_assoc, IsUnit.val_inv_mul, mul_one]
  have r00 : aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) = aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * (ξ * η) := by
    rw [hξη, ← map_mul, e00]
  have r'11 : aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) = ξ * η * aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) := by
    rw [hξη, ← map_mul, e11]
  have r01 : aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) = aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) := by rw [e01]
  have r10 : aA ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) = aA ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) := by rw [e10]
  have rel : N * D' = ξ * η * (D * N') := by
    simp only [hN, hD, hN', hD', r00, r'11, r01, r10]; ring
  refine ⟨ξ', η', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hξη]
    have e : ξ' * η' * (D * N') = ξ * η * (D * N') := by
      rw [← rel, ← hξ'D, ← hη'N]; ring
    exact (hDu.mul hN'u).mul_left_injective e
  · exact isUnit_pow_sub_one_of_mul_eq (r := r) ξ' D N hξ'D (isUnit_frob2 hdvr π hπ hres hAn η hηu _ _ _ _ h01 h00 h10)
  · exact isUnit_pow_sub_one_of_mul_eq (r := r) η' N' D' hη'N (isUnit_frob2 hdvr π hπ hres hAn ξ hξu _ _ _ _ h'10 h'11 h'01)
  · intro B _ _ x d hd
    obtain ⟨hB, hxξη, hxξu, hxηu⟩ := point_facts (r := r) π n x
    have hcol0 := col_identity (𝒪 := 𝒪) g⁻¹ 1 g₁ (c * (unitK K π hπ0)⁻¹) (m : Matrix (Fin 2) (Fin 2) 𝒪) (by
      rw [Units.val_one, mul_one, ← coe_map, ← Units.val_mul, hmat0, Units.val_mul])
      ((stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
      ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
      (by rw [Units.val_one, Matrix.one_mulVec]; rfl) (by rw [Units.val_one, Matrix.one_mulVec]; rfl)
      (fun j => ((![latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0),
        latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)] j :
          ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K))
      (by intro j; fin_cases j <;> rfl)
    have hcol1 := col_identity (𝒪 := 𝒪) g⁻¹ g₁ 1 c (m' : Matrix (Fin 2) (Fin 2) 𝒪) (by
      rw [Units.val_one, mul_one, ← coe_map, ← Units.val_mul, ← Units.val_mul, hmat1])
      ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) : ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
      ((latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1) : ↥(FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K)
      rfl rfl
      (fun j => ((![stdBasisVec (𝒪 := 𝒪) K 0, stdBasisVec (𝒪 := 𝒪) K 1] j : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K))
      (by intro j; fin_cases j <;> (rw [Units.val_one, Matrix.one_mulVec]; rfl))
    have t0 := line_pullback_eq π d g⁻¹ (stdFullLattice K) (FullLattice.act g₁ (stdFullLattice K)) _ hrel0
      (stdBasisVec K 0) (stdBasisVec K 1)
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0))
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)) (m : Matrix (Fin 2) (Fin 2) 𝒪) hcol0 _ _
      (hd.2.1.trans (map_span_eq g₁ _ _))
    have t1 := line_pullback_eq π d g⁻¹ (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K) c hrel1
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0))
      (latticeMapEquiv g₁ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1))
      (stdBasisVec K 0) (stdBasisVec K 1) (m' : Matrix (Fin 2) (Fin 2) 𝒪) hcol1 _ _ hd.1
    constructor
    · rw [t0]
      have e : (algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) * 1 + algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) = x N ∧
          (algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) * 1 + algebraMap 𝒪 B ((m : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) = x D := by
        constructor <;> simp only [hN, hD, haA, map_add, map_mul, AlgHom.commutes, mul_one] <;>
          first | rfl | (rw [add_comm]; rfl)
      rw [e.1, e.2]
      exact span_pair_eq _ _ _ _ _ (hDu.map x) (by rw [← map_mul, hξ'D])
    · rw [t1, map_span_eq]
      have e : (algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 0) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) +
            algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 0 1) * 1) = x N' ∧
          (algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 0) *
            (x.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r) +
            algebraMap 𝒪 B ((m' : Matrix (Fin 2) (Fin 2) 𝒪) 1 1) * 1) = x D' := by
        constructor <;> simp only [hN', hD', haA, map_add, map_mul, AlgHom.commutes, mul_one] <;> rfl
      rw [e.1, e.2]
      exact span_pair_eq' _ _ _ _ _ (hN'u.map x) (by rw [← map_mul, hη'N])
  ·
    refine (Associated.symm ⟨hN'u.unit * hDu.unit⁻¹, ?_⟩)
    rw [Units.val_mul, hξ', ← mul_assoc]
    congr 1
    rw [IsUnit.unit_spec, hN, hN', r01, r00]; ring
  ·
    refine (Associated.symm ⟨hDu.unit * hN'u.unit⁻¹, ?_⟩)
    rw [Units.val_mul, hη', ← mul_assoc]
    congr 1
    rw [IsUnit.unit_spec, hD', hD, r10, r'11]; ring

end TransportPoint

section Assembly

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
variable (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (n : ℕ)

def mkPoint (ξ' η' : An 𝒪 π r n) (h1 : ξ' * η' = algebraMap 𝒪 (An 𝒪 π r n) π) (h2 : IsUnit (ξ' ^ (r - 1) - 1))
    (h3 : IsUnit (η' ^ (r - 1) - 1)) : (chartE 𝒪 π r).obj (An 𝒪 π r n) :=
  ⟨(ξ', η'), h1, h2, h3⟩

include hdvr hπ hres hg₁ in

theorem isPullback_of_TP (g : GL (Fin 2) K) (ξ' η' : An 𝒪 π r n) (h1 : ξ' * η' = algebraMap 𝒪 (An 𝒪 π r n) π)
    (h2 : IsUnit (ξ' ^ (r - 1) - 1)) (h3 : IsUnit (η' ^ (r - 1) - 1)) (htp : TP π g₁ n g ξ' η')
    (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B)
    (hd : IsECH π g₁ n d x) (hd' : IsECH π g₁ n d' (x.comp (liftE π n (mkPoint π n ξ' η' h1 h2 h3)))) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d' := by
  haveI := hdvr
  obtain ⟨e0, e1⟩ := htp B x d hd
  have hd'0 : d'.line (stdFullLattice K) = Submodule.span B {x ξ' ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} := by
    have h := hd'.1
    have e : (x.comp (liftE π n (mkPoint π n ξ' η' h1 h2 h3))).comp
        (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r) = x ξ' := by
      show x (liftE π n _ (xiA 𝒪 π r n)) = x ξ'
      rw [liftE_xi]
      rfl
    rwa [e] at h
  have hd'1 : d'.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + x η' ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice K)).toLinearMap := by
    have h := hd'.2.1
    have e : (x.comp (liftE π n (mkPoint π n ξ' η' h1 h2 h3))).comp
        (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r) = x η' := by
      show x (liftE π n _ (etaA 𝒪 π r n)) = x η'
      rw [liftE_eta]
      rfl
    rwa [e] at h
  have heq : DeligneDatum.pullback π B g⁻¹ d = d' :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d' (DeligneDatum.pullback π B g⁻¹ d)
      (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K) hd'.2.2 (e0.trans hd'0.symm) (e1.trans hd'1.symm)
  rw [← heq]
  exact DeligneDatum.isPullback_pullback π B g⁻¹ d

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem gact_mul (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (g * h)⁻¹ d = DeligneDatum.pullback π B g⁻¹ (DeligneDatum.pullback π B h⁻¹ d) :=
  (Omega.action K π).act_mul B g h d

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem gact_one (B : Type) [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (1 : GL (Fin 2) K)⁻¹ d = d :=
  (Omega.action K π).act_one B d

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem eq_gact_of_isPullback (B : Type) [CommRing B] [Algebra 𝒪 B] (g : GL (Fin 2) K) (d d' : DeligneDatum (K := K) π B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d') : d' = DeligneDatum.pullback π B g⁻¹ d :=
  DeligneDatum.ext' (funext fun M => h M)

include hdvr hπ hres hg₁ in

theorem comp_eq_id_of_TP (g g' : GL (Fin 2) K) (hgg' : g' = g⁻¹)
    (u v : An 𝒪 π r n →ₐ[𝒪] An 𝒪 π r n)
    (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B),
      IsECH π g₁ n d x → IsECH π g₁ n d' (x.comp u) → DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d')
    (hv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B),
      IsECH π g₁ n d x → IsECH π g₁ n d' (x.comp v) → DeligneDatum.IsPullback (K := K) (π := π) B g'⁻¹ d d') :
    v.comp u = AlgHom.id 𝒪 (An 𝒪 π r n) := by
  obtain ⟨d₀, hd₀⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ (AlgHom.id 𝒪 (An 𝒪 π r n))
  obtain ⟨d₁, hd₁⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ v
  obtain ⟨d₂, hd₂⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ (v.comp u)
  have h1 := eq_gact_of_isPullback π _ g' d₀ d₁ (hv _ (AlgHom.id 𝒪 _) d₀ d₁ hd₀ hd₁)
  have h2 := eq_gact_of_isPullback π _ g d₁ d₂ (hu _ v d₁ d₂ hd₁ hd₂)
  have h3 : d₂ = d₀ := by rw [h2, h1, ← gact_mul, hgg', mul_inv_cancel, gact_one]
  rw [h3] at hd₂
  obtain ⟨eξ, eη⟩ := point_eq_of_isECH hd₂ hd₀
  exact algHom_ext_An π n _ _ eξ eη

omit [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem vertex_act_inv (g : GL (Fin 2) K) {v w : Vertex 𝒪 K} (h : Vertex.act g v = w) : Vertex.act g⁻¹ w = v := by
  rw [← h, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

include hdvr hπ hres hg₁ in

theorem exists_TP (g : GL (Fin 2) K)
    (hg : (Vertex.act g (stdVertex 𝒪 K) = stdVertex 𝒪 K ∧
        Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = Vertex.act g₁ (stdVertex 𝒪 K)) ∨
      (Vertex.act g (stdVertex 𝒪 K) = Vertex.act g₁ (stdVertex 𝒪 K) ∧
        Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K)) = stdVertex 𝒪 K)) :
    ∃ ξ' η' : An 𝒪 π r n, ξ' * η' = algebraMap 𝒪 (An 𝒪 π r n) π ∧ IsUnit (ξ' ^ (r - 1) - 1) ∧ IsUnit (η' ^ (r - 1) - 1) ∧
      TP π g₁ n g ξ' η' := by
  rcases hg with hA | hB
  · obtain ⟨ξ', η', h1, h2, h3, h4, -, -⟩ := transportPoint_A hdvr π hπ hres g₁ hg₁ n g hA
    exact ⟨ξ', η', h1, h2, h3, h4⟩
  · obtain ⟨ξ', η', h1, h2, h3, h4, -, -⟩ := transportPoint_B hdvr π hπ hres g₁ hg₁ n g hB
    exact ⟨ξ', η', h1, h2, h3, h4⟩

include hdvr hπ hres hg₁ in

theorem agree_of_transport (g : GL (Fin 2) K) (u v : An 𝒪 π r n →ₐ[𝒪] An 𝒪 π r n)
    (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B),
      IsECH π g₁ n d x → IsECH π g₁ n d' (x.comp u) → DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d')
    (hv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : An 𝒪 π r n →ₐ[𝒪] B) (d d' : DeligneDatum (K := K) π B),
      IsECH π g₁ n d x → IsECH π g₁ n d' (x.comp v) → DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d') :
    v (xiA 𝒪 π r n) = u (xiA 𝒪 π r n) ∧ v (etaA 𝒪 π r n) = u (etaA 𝒪 π r n) := by
  obtain ⟨d₀, hd₀⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ (AlgHom.id 𝒪 (An 𝒪 π r n))
  obtain ⟨d₁, hd₁⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ v
  obtain ⟨d₂, hd₂⟩ := exists_isECH (K := K) π g₁ n hdvr hπ hres hg₁ u
  have e1 := eq_gact_of_isPullback π _ g d₀ d₁ (hv _ (AlgHom.id 𝒪 _) d₀ d₁ hd₀ hd₁)
  have e2 := eq_gact_of_isPullback π _ g d₀ d₂ (hu _ (AlgHom.id 𝒪 _) d₀ d₂ hd₀ hd₂)
  rw [e1.trans e2.symm] at hd₁
  exact point_eq_of_isECH hd₁ hd₂

end Assembly

end F2AlphaEdge
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge.F2AlphaEdge"

open F2AlphaEdge in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)))
    (n : ℕ) :
    ∃! α : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ≃ₐ[𝒪] ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})),
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
        (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
        (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        (d'.line (stdFullLattice K₀) =
          Submodule.span B {(((xq.comp α.toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (((xq.comp α.toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' := by
  haveI := hdvr
  have hginv : (Vertex.act g⁻¹ (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀ ∧
        Vertex.act g⁻¹ (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act g₁ (stdVertex 𝒪 K₀)) ∨
      (Vertex.act g⁻¹ (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) ∧
        Vertex.act g⁻¹ (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀) := by
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨vertex_act_inv g h1, vertex_act_inv g h2⟩
    · exact Or.inr ⟨vertex_act_inv g h2, vertex_act_inv g h1⟩
  obtain ⟨ξ', η', h1, h2, h3, htp⟩ := exists_TP hdvr π hπ hres g₁ hg₁ n g hg
  obtain ⟨ξ'', η'', h1', h2', h3', htp'⟩ := exists_TP hdvr π hπ hres g₁ hg₁ n g⁻¹ hginv
  have hu := isPullback_of_TP hdvr π hπ hres g₁ hg₁ n g ξ' η' h1 h2 h3 htp
  have hv := isPullback_of_TP hdvr π hπ hres g₁ hg₁ n g⁻¹ ξ'' η'' h1' h2' h3' htp'
  have hvu := comp_eq_id_of_TP hdvr π hπ hres g₁ hg₁ n g g⁻¹ rfl _ _ hu hv
  have huv := comp_eq_id_of_TP hdvr π hπ hres g₁ hg₁ n g⁻¹ g (inv_inv g).symm _ _ hv hu
  refine ⟨AlgEquiv.ofAlgHom _ _ huv hvu, ?_, ?_⟩
  · intro B _ _ xq d d' hd hd'
    exact hu B xq d d' hd hd'
  · intro α₁ hα₁
    apply AlgEquiv.coe_algHom_injective
    obtain ⟨eξ, eη⟩ := agree_of_transport hdvr π hπ hres g₁ hg₁ n g _ α₁.toAlgHom hu
      (fun B _ _ x d d' hd hd' => hα₁ B x d d' hd hd')
    exact algHom_ext_An π n _ _ eξ eη

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge.F2AlphaEdge"

end S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge (solution)
