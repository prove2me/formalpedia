-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d5e625ac-8f85-59d2-9da2-411f6e113b8f

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace PIAux

open TensorProduct Polynomial

section Generation

variable {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q]

theorem eq_top_of_mem_of_forall_not_mem_smul_top [Module.Invertible R Q] (N : Submodule R Q) (q : Q)
    (hqN : q ∈ N) (hq : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → q ∉ (𝔪 • ⊤ : Submodule R Q)) : N = ⊤ := by
  set A : Ideal R := N.colon (Set.univ : Set Q) with hA_def
  by_cases hA : A = ⊤
  · have h1 : (1 : R) ∈ A := by rw [hA]; exact Submodule.mem_top
    rw [hA_def, Submodule.mem_colon] at h1
    refine eq_top_iff.mpr fun m _ => ?_
    have := h1 m (Set.mem_univ m)
    rwa [one_smul] at this
  · exfalso
    obtain ⟨𝔪, h𝔪, hA𝔪⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔪 q (hq 𝔪 h𝔪)
    obtain ⟨c, hc⟩ := (Module.Invertible.toModuleEnd_bijective R Q).2 (LinearMap.smulRight φ q)
    have hc' : ∀ x : Q, c • x = φ x • q := fun x => by
      have := congrArg (fun f : Module.End R Q => f x) hc
      simp only [LinearMap.smulRight_apply] at this
      exact this
    have hcA : c ∈ A := by
      rw [hA_def, Submodule.mem_colon]
      intro m _
      rw [hc' m]
      exact N.smul_mem _ hqN
    have hkey : (φ q - c) * φ q = 0 := by
      have h := congrArg φ (hc' q)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
      rw [sub_mul, ← h, sub_self]
    have hmem : (φ q - c) * φ q ∈ 𝔪 := by rw [hkey]; exact 𝔪.zero_mem
    rcases h𝔪.isPrime.mem_or_mem hmem with h1 | h1
    · apply hφ
      have : φ q = (φ q - c) + c := by ring
      rw [this]
      exact 𝔪.add_mem h1 (hA𝔪 hcA)
    · exact hφ h1

theorem mem_sup_smul_top_of_mkQ_mem {V : Type} [AddCommGroup V] [Module R V] (N : Submodule R V) (I : Ideal R)
    (x : V) (hx : N.mkQ x ∈ (I • ⊤ : Submodule R (V ⧸ N))) : x ∈ N ⊔ (I • ⊤ : Submodule R V) := by
  have : x ∈ ((I • ⊤ : Submodule R V).map N.mkQ).comap N.mkQ := by
    rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hx
  rwa [Submodule.comap_map_mkQ] at this

variable {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem surjective_mkQ_comp_of_generator (N : Submodule R W) [Module.Invertible R (W ⧸ N)] (f : V →ₗ[R] W) (v : V)
    (hv : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → f v ∉ N ⊔ (𝔪 • ⊤ : Submodule R W)) :
    Function.Surjective (N.mkQ ∘ₗ f) := by
  rw [← LinearMap.range_eq_top]
  apply eq_top_of_mem_of_forall_not_mem_smul_top _ (N.mkQ (f v)) (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  intro 𝔪 h𝔪 hmem
  exact hv 𝔪 h𝔪 (mem_sup_smul_top_of_mkQ_mem _ _ _ hmem)

theorem comap_eq_ker_mkQ_comp (N : Submodule R W) (f : V →ₗ[R] W) : N.comap f = LinearMap.ker (N.mkQ ∘ₗ f) := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

def quotComapEquiv (N : Submodule R W) (f : V →ₗ[R] W) (hf : Function.Surjective (N.mkQ ∘ₗ f)) :
    (V ⧸ N.comap f) ≃ₗ[R] (W ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (comap_eq_ker_mkQ_comp N f)).trans (LinearMap.quotKerEquivOfSurjective _ hf)

theorem invertible_quot_comap (N : Submodule R W) [Module.Invertible R (W ⧸ N)] (f : V →ₗ[R] W)
    (hf : Function.Surjective (N.mkQ ∘ₗ f)) : Module.Invertible R (V ⧸ N.comap f) :=
  Module.Invertible.congr (quotComapEquiv N f hf).symm

theorem eq_of_le_of_invertible (N₁ N₂ : Submodule R V) [Module.Invertible R (V ⧸ N₁)] [Module.Invertible R (V ⧸ N₂)]
    (hle : N₁ ≤ N₂) : N₁ = N₂ := by
  apply le_antisymm hle
  have hle' : N₁ ≤ N₂.comap (LinearMap.id : V →ₗ[R] V) := by rw [Submodule.comap_id]; exact hle
  let f : (V ⧸ N₁) →ₗ[R] (V ⧸ N₂) := Submodule.mapQ _ _ LinearMap.id hle'
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => Submodule.mapQ_apply _ _ _ x
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, hf x⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  intro x hx
  have h0 : f (Submodule.Quotient.mk x) = 0 := by
    rw [hf]; exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have h1 : (Submodule.Quotient.mk x : V ⧸ N₁) = 0 := hinj (by rw [h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

theorem smul_mem_iff_of_isUnit (N : Submodule R V) {r : R} (hr : IsUnit r) (x : V) : r • x ∈ N ↔ x ∈ N := by
  refine ⟨fun h => ?_, fun h => N.smul_mem r h⟩
  obtain ⟨u, rfl⟩ := hr
  have : x = (↑u⁻¹ : R) • ((u : R) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact N.smul_mem _ h

end Generation

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

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply IsFractionRing.injective 𝒪 K
  rw [algebraMap_coordEquiv]
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

private def _root_.PIAux.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "PIAux" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem apply_mem_of_mem_sup_smul_top {X : Type} [AddCommGroup X] [Module B X] (D : X →ₗ[B] B)
    (P : Submodule B X) (hP : ∀ y ∈ P, D y = 0) (𝔭 : Ideal B) {x : X}
    (hx : x ∈ P ⊔ (𝔭 • ⊤ : Submodule B X)) : D x ∈ 𝔭 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, hP y hy, zero_add]
  refine Submodule.smul_induction_on (p := fun z => D z ∈ 𝔭) hz (fun r hr n _ => ?_) (fun a c ha hc => ?_)
  · show D (r • n) ∈ 𝔭
    rw [LinearMap.map_smul, smul_eq_mul]; exact Ideal.mul_mem_right (D n) 𝔭 hr
  · show D (a + c) ∈ 𝔭
    rw [map_add]; exact 𝔭.add_mem ha hc

theorem decomp (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    x = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) := by
  have h := (tensorBasis (K := K) B).sum_repr x
  rw [Fin.sum_univ_two] at h
  have hsb : ∀ i : Fin 2, (stdBasis (𝒪 := 𝒪) (K := K)) i = stdBasisVec K i := by
    intro i
    rw [stdBasis, Module.Basis.coe_ofEquivFun]
    show coordEquiv.symm (Pi.single i (1 : 𝒪) : Fin 2 → 𝒪) = stdBasisVec K i
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [coordEquiv_stdBasisVec]
  have hb : ∀ i : Fin 2, (tensorBasis (K := K) B) i = (1 : B) ⊗ₜ[𝒪] stdBasisVec K i := by
    intro i
    rw [tensorBasis, Algebra.TensorProduct.basis_apply, hsb]
  rw [hb 0, hb 1] at h
  exact h.symm

end Coord

section Engine

variable {B : Type} [CommRing B] {V : Type} [AddCommGroup V] [Module B V]

theorem line_eq_span (N : Submodule B V) [Module.Invertible B (V ⧸ N)] (u w : V) (cu cw : V →ₗ[B] B)
    (hdec : ∀ x, x = cu x • u + cw x • w)
    (hgen : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → u ∉ N ⊔ (𝔪 • ⊤ : Submodule B V)) :
    ∃ ξ : B, N = Submodule.span B {ξ • u + w} ∧ ∀ b : B, b • u ∈ N → b = 0 := by
  set f : B →ₗ[B] V := (LinearMap.id : B →ₗ[B] B).smulRight u with hf
  have hfapp : ∀ b : B, f b = b • u := fun b => by rw [hf, LinearMap.smulRight_apply, LinearMap.id_apply]
  have hsurj : Function.Surjective (N.mkQ ∘ₗ f) :=
    surjective_mkQ_comp_of_generator N f (1 : B) (fun 𝔪 h𝔪 => by rw [hfapp, one_smul]; exact hgen 𝔪 h𝔪)
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  have hinj : ∀ b : B, b • u ∈ N → b = 0 := by
    intro b hb
    apply hbij.1
    rw [map_zero, LinearMap.comp_apply, hfapp, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero N).2 hb
  obtain ⟨c, hc⟩ := hsurj (N.mkQ w)
  rw [LinearMap.comp_apply, hfapp, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hc

  have hmem : (-c) • u + w ∈ N := by
    have : (-c) • u + w = -(c • u - w) := by rw [neg_smul, neg_sub, sub_eq_neg_add]
    rw [this]; exact N.neg_mem hc
  refine ⟨-c, le_antisymm ?_ ?_, hinj⟩
  · intro x hx
    rw [Submodule.mem_span_singleton]
    set a := cu x with ha
    set b := cw x with hb
    have hx' : x = a • u + b • w := by rw [ha, hb]; exact hdec x
    refine ⟨b, ?_⟩
    have h1 : (a + b * c) • u ∈ N := by
      have : (a + b * c) • u = x - b • ((-c) • u + w) := by rw [hx']; module
      rw [this]; exact N.sub_mem hx (N.smul_mem _ hmem)
    have h2 := hinj _ h1
    have h3 : a = -(b * c) := by linear_combination h2
    rw [hx', h3]; module
  · rw [Submodule.span_singleton_le_iff_mem]; exact hmem

end Engine

section Residue

variable {𝒪 : Type} [CommRing 𝒪]

theorem pow_sub_mem_span [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (a : 𝒪) : a ^ q - a ∈ Ideal.span {π} := by
  haveI : (Ideal.span {π}).IsMaximal := by rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal 𝒪
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = q := by rw [← Nat.card_eq_fintype_card]; exact hq
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
  have := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {π}) a)
  rwa [hcard] at this

theorem isUnit_of_not_dvd [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) {a : 𝒪}
    (ha : ¬ π ∣ a) : IsUnit a := by
  by_contra h
  apply ha
  have : a ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal a).mpr h
  rw [hπ.maximalIdeal_eq] at this
  exact Ideal.mem_span_singleton.mp this

theorem prod_univ_X_sub_C {k : Type} [Field k] [Fintype k] :
    (Finset.univ.val.map fun c : k => X - Polynomial.C c).prod = (X ^ Fintype.card k - X : k[X]) := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hmonic : (X ^ Fintype.card k - X : k[X]).Monic :=
    (monic_X_pow _).sub_of_left (by rw [degree_X_pow, degree_X]; exact_mod_cast hq1)
  have hcr : Multiset.card (X ^ Fintype.card k - X : k[X]).roots = (X ^ Fintype.card k - X : k[X]).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X k, FiniteField.X_pow_card_sub_X_natDegree_eq k hq1]
    exact Finset.card_univ
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcr
  rwa [FiniteField.roots_X_pow_card_sub_X k] at h

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem pow_pred_sub_one_not_mem [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq2 : 2 ≤ q) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (ξ : B)
    (hξ : ∀ a : 𝒪, ¬ π ∣ a → ξ - algebraMap 𝒪 B a ∉ 𝔭) : ξ ^ (q - 1) - 1 ∉ 𝔭 := by
  classical
  intro hmem
  haveI : (Ideal.span {π}).IsMaximal := by rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal 𝒪
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = q := by rw [← Nat.card_eq_fintype_card]; exact hq
  haveI : Nontrivial (B ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭.ne_top
  haveI : IsDomain (B ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭

  set ι : 𝒪 ⧸ Ideal.span {π} →+* B ⧸ 𝔭 :=
    Ideal.Quotient.lift (Ideal.span {π}) ((Ideal.Quotient.mk 𝔭).comp (algebraMap 𝒪 B)) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact 𝔭.mul_mem_left _ hπ𝔭) with hι
  have hι_mk : ∀ a : 𝒪, ι (Ideal.Quotient.mk (Ideal.span {π}) a) = Ideal.Quotient.mk 𝔭 (algebraMap 𝒪 B a) :=
    fun a => rfl
  set x : B ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 ξ with hx
  have hx1 : x ^ (q - 1) = 1 := by
    rw [← sub_eq_zero, hx, ← map_pow, ← map_one (Ideal.Quotient.mk 𝔭), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem

  have hprod : ∏ c : 𝒪 ⧸ Ideal.span {π}, (x - ι c) = 0 := by
    have h := congrArg (fun p => Polynomial.eval x (Polynomial.map ι p))
      (prod_univ_X_sub_C (k := 𝒪 ⧸ Ideal.span {π}))
    simp only [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.map_pow, Polynomial.eval_pow,
      hcard] at h
    rw [← Finset.prod_eq_multiset_prod] at h
    rw [h, show x ^ q = x ^ (q - 1) * x by rw [← pow_succ, Nat.sub_add_cancel (by omega)], hx1, one_mul, sub_self]
  obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hprod
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [hι_mk, hx, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hc
  by_cases ha : π ∣ a
  ·
    obtain ⟨a', rfl⟩ := ha
    have hξ𝔭 : ξ ∈ 𝔭 := by
      have : ξ = (ξ - algebraMap 𝒪 B (π * a')) + algebraMap 𝒪 B π * algebraMap 𝒪 B a' := by rw [map_mul]; ring
      rw [this]; exact 𝔭.add_mem hc (𝔭.mul_mem_right _ hπ𝔭)
    apply h𝔭.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : B) = ξ ^ (q - 1) - (ξ ^ (q - 1) - 1) := by ring
    rw [this]
    exact 𝔭.sub_mem (𝔭.pow_mem_of_mem hξ𝔭 (q - 1) (by omega)) hmem
  · exact hξ a ha hc

theorem isUnit_of_forall_not_mem {x : B} (h : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → x ∉ 𝔭) : IsUnit x := by
  by_contra hx
  obtain ⟨𝔪, h𝔪, hx𝔪⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
  exact h 𝔪 h𝔪.isPrime hx𝔪

end Residue

end PIAux

end

open PIAux in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)) :
    ∃ x : chartERing 𝒪 π q →ₐ[𝒪] B,
      d.line (stdFullLattice K) =
        Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
      d.line (FullLattice.act g (stdFullLattice K)) =
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
          (actBaseChange B g (stdFullLattice K)).toLinearMap := by
  classical

  have q2 : 2 ≤ q := by
    rw [← hq]
    haveI : Nontrivial (𝒪 ⧸ Ideal.span {π}) :=
      nontrivial_of_ne 0 1 (Ideal.Quotient.zero_ne_one_iff.2
        (fun h => hπ.not_isUnit (Ideal.span_singleton_eq_top.1 h)))
    exact Finite.one_lt_card
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπmem : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → algebraMap 𝒪 B π ∈ 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨n, hn⟩ := hB
    exact h𝔭.mem_of_pow_mem n (by rw [hn]; exact 𝔭.zero_mem)
  have hgv : ∀ w : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K).mulVec w = ![algebraMap 𝒪 K π * w 0, w 1] := by
    intro w; rw [hg]; ext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]
  have hM₁le : (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
    rw [hgv]
    intro i
    fin_cases i
    · obtain ⟨a, ha⟩ := hw 0
      exact ⟨π * a, by simp [← ha, map_mul]⟩
    · simpa using hw 1

  have hnotM₁ : ∀ (a : 𝒪), ¬ π ∣ a → ∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v : Fin 2 → K) 0 = algebraMap 𝒪 K a →
      (v : Fin 2 → K) ∉ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    intro a ha v hv0 hmem
    obtain ⟨w, hw, hgw⟩ := mem_latticeMap.mp hmem
    obtain ⟨c, hc⟩ := hw 0
    have h0 := congrFun hgw 0
    rw [hgv, hv0] at h0
    apply ha
    refine ⟨c, IsFractionRing.injective 𝒪 K ?_⟩
    rw [map_mul, hc]; simpa using h0.symm

  have hnotπM₀ : ∀ (b : 𝒪), ¬ π ∣ b → ∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v : Fin 2 → K) 1 = algebraMap 𝒪 K b →
      ¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 v : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
        algebraMap 𝒪 K π • (w : Fin 2 → K) := by
    intro b hb v hv1
    rintro ⟨w, hw⟩
    rw [coe_latticeMapEquiv_apply, hgv] at hw
    have h1 := congrFun hw 1
    obtain ⟨c, hc⟩ := w.2 1
    apply hb
    refine ⟨c, IsFractionRing.injective 𝒪 K ?_⟩
    rw [map_mul, hc, ← hv1]; simpa [Algebra.smul_def] using h1

  have he₀0 : ((stdBasisVec K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) 0 = algebraMap 𝒪 K 1 := by
    show (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0 = _; simp
  have he₁1 : ((stdBasisVec K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) 1 = algebraMap 𝒪 K 1 := by
    show (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1 = _; simp
  have h1ndvd : ¬ π ∣ (1 : 𝒪) := fun h => hπu (isUnit_of_dvd_one h)

  haveI hI₀ : Module.Invertible B ((latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) ⧸ d.line (stdFullLattice (𝒪 := 𝒪) K)) := d.invertible (stdFullLattice (𝒪 := 𝒪) K)
  have hgen₀ : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal →
      (1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 ∉ d.line (stdFullLattice (𝒪 := 𝒪) K) ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) :=
    fun 𝔪 h𝔪 => (hd 𝔪 h𝔪.isPrime).2.2.1 (stdBasisVec K 0) (hnotM₁ 1 h1ndvd _ he₀0)
  obtain ⟨ξ, hN₀, hinj₀⟩ := PIAux.line_eq_span (d.line (stdFullLattice (𝒪 := 𝒪) K)) ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0)
    ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) (PIAux.coord B 0) (PIAux.coord B 1) (PIAux.decomp B) hgen₀

  set N₁' : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) := (d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))).comap (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap with hN₁'def
  have hmapN₁ : N₁'.map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap = d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)) :=
    Submodule.map_comap_eq_of_surjective (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).surjective _
  haveI hI₁ : Module.Invertible B ((latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) ⧸ N₁') := by
    haveI := d.invertible (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))
    exact Module.Invertible.congr (Submodule.Quotient.equiv N₁' (d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))) (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)) hmapN₁).symm
  have hpush : ∀ (𝔭 : Ideal B) (x : (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))), x ∈ N₁' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) →
      (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)) x ∈ d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)) ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)))) := by
    intro 𝔭 x hx
    have hle : (N₁' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)))).map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap ≤
        d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)) ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)))) := by
      rw [Submodule.map_sup, hmapN₁, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    exact hle (Submodule.mem_map_of_mem hx)
  have hgen₁ : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal →
      (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1 ∉ N₁' ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) := by
    intro 𝔪 h𝔪 hmem
    apply (hd 𝔪 h𝔪.isPrime).2.2.2 (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)) (hnotπM₀ 1 h1ndvd _ he₁1)
    exact hpush 𝔪 _ hmem
  have hdec' : ∀ x : (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)), x = PIAux.coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) +
      PIAux.coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) := fun x => by
    rw [add_comm]; exact PIAux.decomp B x
  obtain ⟨η, hN₁, hinj₁⟩ := PIAux.line_eq_span N₁' ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1)
    ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) (PIAux.coord B 1) (PIAux.coord B 0) hdec' hgen₁

  have hge₀ : (⟨((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K),
      hM₁le (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0)).2⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) = π • stdBasisVec K 0 := by
    apply Subtype.ext
    show ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      π • ((stdBasisVec K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [coe_latticeMapEquiv_apply, hgv]
    show (![algebraMap 𝒪 K π * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0, (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1] : Fin 2 → K) =
      π • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)
    ext i; fin_cases i <;> simp [Algebra.smul_def]
  have hge₁ : (⟨((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1) : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K),
      hM₁le (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)).2⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) = stdBasisVec K 1 := by
    apply Subtype.ext
    show ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1) : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((stdBasisVec K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [coe_latticeMapEquiv_apply, hgv]
    show (![algebraMap 𝒪 K π * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0, (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1] : Fin 2 → K) =
      (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)
    ext i; fin_cases i <;> simp
  have hAe : ∀ i : Fin 2, inclBaseChange B hM₁le ((actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)) ((1 : B) ⊗ₜ[𝒪] stdBasisVec K i)) =
      (1 : B) ⊗ₜ[𝒪] (⟨((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K i) : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K),
        hM₁le (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K i)).2⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :=
    fun i => rfl
  have hξη : ξ * η = algebraMap 𝒪 B π := by
    have hw₁ : (1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + η • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) ∈ N₁' := by
      rw [hN₁, add_comm]; exact Submodule.mem_span_singleton_self _
    have hmem : inclBaseChange B hM₁le ((actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)) ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + η • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1))) ∈
        d.line (stdFullLattice (𝒪 := 𝒪) K) :=
      d.mono hM₁le (Submodule.mem_map_of_mem (by rw [← hmapN₁]; exact Submodule.mem_map_of_mem hw₁))
    rw [map_add, map_smul, map_add, map_smul, hAe, hAe, hge₀, hge₁, TensorProduct.tmul_smul, ← algebraMap_smul B π, hN₀,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h0 := congrArg (PIAux.coord B 0) hr
    have h1 := congrArg (PIAux.coord B 1) hr
    simp only [map_add, map_smul, PIAux.coord_tmul_stdBasisVec, smul_eq_mul] at h0 h1
    simp at h0 h1
    rw [← h0, ← h1, mul_comm]

  have hξunit : IsUnit (ξ ^ (q - 1) - 1) := by
    refine PIAux.isUnit_of_forall_not_mem fun 𝔭 h𝔭 => PIAux.pow_pred_sub_one_not_mem π hπ q hq q2 𝔭 h𝔭 (hπmem 𝔭 h𝔭) ξ ?_
    intro a ha hmem

    apply (hd 𝔭 h𝔭).2.2.1 (a • stdBasisVec K 0 + stdBasisVec K 1) (hnotM₁ a ha _ ?_)
    · rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, ← algebraMap_smul B a,
        show algebraMap 𝒪 B a • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1 =
          (ξ • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) +
            (algebraMap 𝒪 B a - ξ) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) by module]
      refine Submodule.add_mem_sup (by rw [hN₀]; exact Submodule.mem_span_singleton_self _)
        (Submodule.smul_mem_smul ?_ Submodule.mem_top)
      rw [← neg_sub]; exact 𝔭.neg_mem hmem
    · show (a • ((stdBasisVec K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) + ((stdBasisVec K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)) 0 = _
      show (a • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) + (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) 0 = _
      simp [Algebra.smul_def]
  have hηunit : IsUnit (η ^ (q - 1) - 1) := by
    refine PIAux.isUnit_of_forall_not_mem fun 𝔭 h𝔭 => PIAux.pow_pred_sub_one_not_mem π hπ q hq q2 𝔭 h𝔭 (hπmem 𝔭 h𝔭) η ?_
    intro b hb hmem

    apply (hd 𝔭 h𝔭).2.2.2 (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0 + b • stdBasisVec K 1)) (hnotπM₀ b hb _ ?_)
    · refine hpush 𝔭 ((1 : B) ⊗ₜ[𝒪] (stdBasisVec K 0 + b • stdBasisVec K 1)) ?_
      rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, ← algebraMap_smul B b,
        show (1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + algebraMap 𝒪 B b • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) =
          (η • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 0) +
            (algebraMap 𝒪 B b - η) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) by module]
      refine Submodule.add_mem_sup (by rw [hN₁]; exact Submodule.mem_span_singleton_self _)
        (Submodule.smul_mem_smul ?_ Submodule.mem_top)
      rw [← neg_sub]; exact 𝔭.neg_mem hmem
    · show (((stdBasisVec K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) + b • ((stdBasisVec K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)) 1 = _
      show ((Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) + b • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) 1 = _
      simp [Algebra.smul_def]

  let pt : (chartE 𝒪 π q).obj B := ⟨(ξ, η), hξη, hξunit, hηunit⟩
  refine ⟨chartERing.lift pt, ?_, ?_⟩
  · rw [chartERing.lift_ξ, hN₀, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · rw [chartERing.lift_η, ← hmapN₁, hN₁, add_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite (solution)
