-- Prove2me | solution 1 for GaloisRep.exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a66a659e-3424-5a7d-8686-2a6d51645101

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct
open WithConv Polynomial

namespace H140

abbrev Zq (q : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev Qb : Type := AlgebraicClosure ℚ

section Base
variable (q : ℕ) [hq : Fact q.Prime]

scoped instance isPrime_span : (Ideal.span {(q : ℤ)}).IsPrime := by
  have hp : Prime (q : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; simpa using hq.out
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

scoped instance isLocalizationZq : IsLocalization.AtPrime (Zq q) (Ideal.span {(q : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt (p := q) hq.out

scoped instance isDVRZq : IsDiscreteValuationRing (Zq q) := by
  have hne : Ideal.span {(q : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.out.ne_zero
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (P := Ideal.span {(q : ℤ)}) hne (Zq q)

theorem algebraMap_Zq_apply (r : Zq q) : algebraMap (Zq q) Qb r = ((r : ℚ) : Qb) := rfl

theorem ringHom_Zq_ext {P : Type*} [CommRing P] (j k : Zq q →+* P) : j = k :=
  IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl (RingHom.ext_int _ _)

omit hq in

theorem nontrivial_of_bialgebra (R A : Type*) [CommSemiring R] [Nontrivial R] [Semiring A] [Bialgebra R A] :
    Nontrivial A := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (Coalgebra.counit (R := R) (A := A)) h
  simp at this

end Base

section Place
variable (q : ℕ) [hq : Fact q.Prime] (Aq : ValuationSubring Qb) [hAq : Fact (Aq.LiesOverPrime q)]

theorem natCast_mem_maximalIdeal : (q : Aq) ∈ IsLocalRing.maximalIdeal Aq := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  have h__af := (hAq.out : (q : Qb) ∈ Aq.nonunits)
  simp at h__af ⊢
  exact h__af

theorem isUnit_natCast_of_coprime {d : ℕ} (hd : d.Coprime q) : IsUnit (d : Aq) := by
  by_contra h
  have hmem : (d : Aq) ∈ IsLocalRing.maximalIdeal Aq := h
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hd : IsCoprime (d : ℤ) (q : ℤ))
  have h1 : (1 : Aq) ∈ IsLocalRing.maximalIdeal Aq := by
    have : (a : Aq) * d + b * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Aq) hab
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem)
      (Ideal.mul_mem_left _ _ (natCast_mem_maximalIdeal q Aq))
  exact (IsLocalRing.maximalIdeal.isMaximal Aq).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem algebraMap_Zq_mem (r : Zq q) : algebraMap (Zq q) Qb r ∈ Aq := by
  rw [algebraMap_Zq_apply, ← ValuationSubring.valuation_le_one_iff, Rat.cast_def, map_div₀]
  have hden : Aq.valuation ((r : ℚ).den : Qb) = 1 := by
    have := (ValuationSubring.valuation_eq_one_iff Aq ((r : ℚ).den : Aq)).mp
      (isUnit_natCast_of_coprime q Aq r.2)
    simpa using this
  have hnum : Aq.valuation ((r : ℚ).num : Qb) ≤ 1 :=
    (Aq.valuation_le_one_iff _).mpr (intCast_mem Aq _)
  rw [hden, div_one]; exact hnum

def toAq : Zq q →+* Aq := (algebraMap (Zq q) Qb).codRestrict Aq (algebraMap_Zq_mem q Aq)

scoped instance algebraZqAq : Algebra (Zq q) Aq := (toAq q Aq).toAlgebra

theorem algebraMap_ZqAq_coe (r : Zq q) : ((algebraMap (Zq q) Aq r : Aq) : Qb) = algebraMap (Zq q) Qb r :=
  rfl

scoped instance isScalarTower_ZqAqQb : @IsScalarTower (Zq q) Aq Qb Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev κ : Type := IsLocalRing.ResidueField Aq

example : Algebra (Zq q) (κ Aq) := inferInstance
example : IsScalarTower (Zq q) Aq (κ Aq) := inferInstance

end Place

section Points
variable (q : ℕ) [hq : Fact q.Prime] (Aq : ValuationSubring Qb) [hAq : Fact (Aq.LiesOverPrime q)]
variable (H : Type) [CommRing H] [HopfAlgebra (Zq q) H] [Module.Finite (Zq q) H]

abbrev Pt : Type := H →ₐ[Zq q] Qb

theorem apply_mem (f : Pt q H) (h : H) : f h ∈ Aq := by
  have hint : IsIntegral (Zq q) (f h) := (Algebra.IsIntegral.isIntegral (R := Zq q) h).map f
  have hint' : IsIntegral Aq (f h) := hint.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Aq) (K := Qb)).mp hint'
  rw [← hy]; exact y.2

def fA (f : Pt q H) : H →ₐ[Zq q] Aq where
  toFun h := ⟨f h, apply_mem q Aq H f h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp [algebraMap_ZqAq_coe])

@[scoped simp] theorem fA_coe (f : Pt q H) (h : H) : ((fA q Aq H f h : Aq) : Qb) = f h := rfl

def valA : Aq →ₐ[Zq q] Qb := IsScalarTower.toAlgHom (Zq q) Aq Qb

@[scoped simp] theorem valA_apply (a : Aq) : valA q Aq a = (a : Qb) := rfl

theorem valA_comp_fA (f : Pt q H) : (valA q Aq).comp (fA q Aq H f) = f := AlgHom.ext fun _ => rfl

theorem comp_valA_injective :
    Function.Injective ((valA q Aq).comp : (H →ₐ[Zq q] Aq) → Pt q H) :=
  fun _ _ h => AlgHom.ext fun x => Subtype.val_injective (AlgHom.congr_fun h x)

def red (f : Pt q H) : H →ₐ[Zq q] κ Aq := (IsScalarTower.toAlgHom (Zq q) Aq (κ Aq)).comp (fA q Aq H f)

theorem red_apply (f : Pt q H) (h : H) : red q Aq H f h = IsLocalRing.residue Aq (fA q Aq H f h) := rfl

theorem fA_mul (f g : WithConv (Pt q H)) :
    fA q Aq H (f * g).ofConv = (toConv (fA q Aq H f.ofConv) * toConv (fA q Aq H g.ofConv)).ofConv := by
  apply comp_valA_injective q Aq H
  rw [valA_comp_fA, AlgHom.comp_convMul_distrib, valA_comp_fA, valA_comp_fA, toConv_ofConv, toConv_ofConv]

theorem red_mul (f g : WithConv (Pt q H)) :
    red q Aq H (f * g).ofConv = (toConv (red q Aq H f.ofConv) * toConv (red q Aq H g.ofConv)).ofConv := by
  simp only [red, fA_mul, AlgHom.comp_convMul_distrib]

theorem fA_one_apply (h : H) :
    fA q Aq H (1 : WithConv (Pt q H)).ofConv h = algebraMap (Zq q) Aq (Coalgebra.counit h) :=
  Subtype.ext (by rw [fA_coe, AlgHom.convOne_apply, algebraMap_ZqAq_coe])

theorem red_one : red q Aq H (1 : WithConv (Pt q H)).ofConv = (1 : WithConv (H →ₐ[Zq q] κ Aq)).ofConv := by
  ext h
  rw [red_apply, AlgHom.convOne_apply, fA_one_apply]
  exact (IsScalarTower.algebraMap_apply (Zq q) Aq (κ Aq) _).symm

def redHom : WithConv (Pt q H) →* WithConv (H →ₐ[Zq q] κ Aq) where
  toFun f := toConv (red q Aq H f.ofConv)
  map_one' := by rw [red_one]
  map_mul' f g := by rw [red_mul]

@[scoped simp] theorem redHom_apply (f : WithConv (Pt q H)) : redHom q Aq H f = toConv (red q Aq H f.ofConv) := rfl

theorem red_eq_one_iff (f : Pt q H) :
    red q Aq H f = (1 : WithConv (H →ₐ[Zq q] κ Aq)).ofConv ↔
      ∀ h : H, Aq.valuation (f h - algebraMap (Zq q) Qb (Coalgebra.counit h)) < 1 := by
  rw [AlgHom.ext_iff]
  refine forall_congr' fun h => ?_
  rw [red_apply, AlgHom.convOne_apply, IsScalarTower.algebraMap_apply (Zq q) Aq (κ Aq), ← sub_eq_zero,
    show algebraMap (↥Aq) (κ Aq) = IsLocalRing.residue Aq from rfl, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  rfl

def galPt (σ : Qb ≃ₐ[ℚ] Qb) (f : Pt q H) : Pt q H :=
  { (σ : Qb →+* Qb).comp (f : H →+* Qb) with
    commutes' := fun r => by
      simp [algebraMap_Zq_apply] }

@[scoped simp] theorem galPt_apply (σ : Qb ≃ₐ[ℚ] Qb) (f : Pt q H) (h : H) : galPt q H σ f h = σ (f h) := rfl

omit hq in

theorem residue_gal_eq (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ Aq.inertiaSubgroupIn ℚ) (a : Qb) (ha : a ∈ Aq)
    (hσa : σ a ∈ Aq) :
    IsLocalRing.residue Aq ⟨σ a, hσa⟩ = IsLocalRing.residue Aq ⟨a, ha⟩ := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
  have h1 : (MulSemiringAction.toRingAut (Aq.decompositionSubgroup ℚ) (IsLocalRing.ResidueField Aq)) τ = 1 := hτ
  have := RingEquiv.congr_fun h1 (IsLocalRing.residue Aq ⟨a, ha⟩)
  simp at this
  exact this

theorem red_galPt (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ Aq.inertiaSubgroupIn ℚ) (f : Pt q H) :
    red q Aq H (galPt q H σ f) = red q Aq H f := by
  ext h
  rw [red_apply, red_apply]
  exact residue_gal_eq Aq σ hσ (f h) (apply_mem q Aq H f h) _

end Points

section Ev
variable (q : ℕ) [hq : Fact q.Prime] (Aq : ValuationSubring Qb) [hAq : Fact (Aq.LiesOverPrime q)]
variable (H : Type) [CommRing H] [HopfAlgebra (Zq q) H] [Module.Finite (Zq q) H] [Module.Flat (Zq q) H]
  [Coalgebra.IsCocomm (Zq q) H]

scoped instance free_H : Module.Free (Zq q) H := Module.free_of_flat_of_isLocalRing

theorem natCard_pt : Nat.card (Pt q H) = Module.finrank (Zq q) H := by
  rw [← GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf q H]
  exact (Nat.card_congr (WithConv.equiv _)).symm

theorem natCard_pt_ne_zero : Nat.card (Pt q H) ≠ 0 := by
  haveI := nontrivial_of_bialgebra (Zq q) H
  rw [natCard_pt]; exact Module.finrank_pos.ne'

scoped instance finite_pt : Finite (Pt q H) := Nat.finite_of_card_ne_zero (natCard_pt_ne_zero q H)

scoped instance fintype_pt : Fintype (Pt q H) := Fintype.ofFinite _

abbrev rk : ℕ := Module.finrank (Zq q) H

def σι : Pt q H ≃ Fin (rk q H) :=
  (Nat.equivFinOfCardPos (natCard_pt_ne_zero q H)).trans (finCongr (natCard_pt q H))

def bH : Module.Basis (Fin (rk q H)) (Zq q) H := Module.finBasis (Zq q) H

def N : Matrix (Fin (rk q H)) (Fin (rk q H)) Qb := fun k j => (σι q H).symm k (bH q H j)

theorem N_isUnit : IsUnit (N q H) := by
  classical
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have hli := linearIndependent_algHom_toLinearMap (Zq q) H Qb
  let Φ : (H →ₗ[Zq q] Qb) →ₗ[Qb] (Fin (rk q H) → Qb) :=
    { toFun := fun L j => L (bH q H j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : LinearMap.ker Φ = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun L hL => (bH q H).ext fun j => congr_fun hL j
  have := (hli.map' Φ hΦ).comp (σι q H).symm (σι q H).symm.injective
  exact this

theorem N_det_ne_zero : (N q H).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (N_isUnit q H)).ne_zero

def NA : Matrix (Fin (rk q H)) (Fin (rk q H)) Aq := fun k j => fA q Aq H ((σι q H).symm k) (bH q H j)

theorem NA_det_ne_zero : (NA q Aq H).det ≠ 0 := by
  intro h
  apply N_det_ne_zero q H
  have hmap : (algebraMap Aq Qb).mapMatrix (NA q Aq H) = N q H := by
    ext k j; rfl
  rw [← hmap, ← RingHom.map_det, h, map_zero]

def ev : Aq ⊗[Zq q] H →ₐ[Aq] (Pt q H → Aq) :=
  Algebra.TensorProduct.lift (Algebra.ofId Aq _) (Pi.algHom (Zq q) _ fun i => fA q Aq H i)
    (fun _ _ => Commute.all _ _)

theorem ev_tmul (a : Aq) (h : H) : ev q Aq H (a ⊗ₜ h) = fun i => a * fA q Aq H i h := by
  rw [ev, Algebra.TensorProduct.lift_tmul]
  rfl

theorem ev_injective : Function.Injective (ev q Aq H) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  let bA := Algebra.TensorProduct.basis (↥Aq) (bH q H)
  have hx' : x = ∑ j, (bA.repr x j) • bA j := (bA.sum_repr x).symm
  have hev : ∀ i : Pt q H, ∑ j, bA.repr x j * fA q Aq H i (bH q H j) = 0 := by
    intro i
    have := congr_fun hx i
    rw [hx', map_sum] at this
    simpa [bA, Algebra.TensorProduct.basis_apply, ev_tmul, Finset.sum_apply] using this
  have hc : (fun j => bA.repr x j) = 0 := by
    refine Matrix.eq_zero_of_mulVec_eq_zero (NA_det_ne_zero q Aq H) (funext fun k => ?_)
    rw [Pi.zero_apply, ← hev ((σι q H).symm k), Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx']
  exact Finset.sum_eq_zero fun j _ => by rw [show bA.repr x j = 0 from congr_fun hc j, zero_smul]

omit hq hAq in

theorem pi_algHom_eq {ι : Type} [Fintype ι] {k : Type} [Field k] [Algebra Aq k]
    (Ψ : (ι → Aq) →ₐ[Aq] k) : ∃ i, ∀ v, Ψ v = algebraMap Aq k (v i) := by
  classical
  have hsum : ∑ i, Ψ (Pi.single i 1) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ : ι => (1 : Aq))]
    exact map_one Ψ
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hidem : Ψ (Pi.single i 1) * Ψ (Pi.single i 1) = Ψ (Pi.single i 1) := by
    rw [← map_mul]; congr 1; ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
  have hone : Ψ (Pi.single i 1) = 1 := mul_left_cancel₀ hi (by rw [hidem, mul_one])
  refine ⟨i, fun v => ?_⟩
  calc Ψ v = Ψ v * Ψ (Pi.single i 1) := by rw [hone, mul_one]
    _ = Ψ (v * Pi.single i 1) := (map_mul Ψ _ _).symm
    _ = Ψ (v i • Pi.single i (1 : Aq)) := by
        congr 1; ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
    _ = v i • Ψ (Pi.single i 1) := map_smul Ψ _ _
    _ = algebraMap Aq k (v i) := by rw [hone, Algebra.smul_def, mul_one]

theorem red_surjective (hκ : IsAlgClosed (κ Aq)) : Function.Surjective (red q Aq H) := by
  classical
  intro φ
  let φ' : Aq ⊗[Zq q] H →ₐ[Aq] κ Aq :=
    Algebra.TensorProduct.lift (Algebra.ofId Aq (κ Aq)) φ (fun _ _ => Commute.all _ _)
  let eT := AlgEquiv.ofInjective (ev q Aq H) (ev_injective q Aq H)
  let ψ₀ : ↥(ev q Aq H).range →ₐ[Aq] κ Aq := φ'.comp (eT.symm : ↥(ev q Aq H).range →ₐ[Aq] _)
  obtain ⟨Ψ, hΨ⟩ := Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed (ev q Aq H).range (κ Aq) ψ₀
  have hΨev : ∀ x, Ψ (ev q Aq H x) = φ' x := fun x => by
    have := AlgHom.congr_fun hΨ (eT x)
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply] at this
    rw [AlgEquiv.ofInjective_apply] at this
    rw [this]
    simp [ψ₀, eT]
  obtain ⟨i, hi⟩ := pi_algHom_eq Aq Ψ
  refine ⟨i, AlgHom.ext fun h => ?_⟩
  have h1 : φ h = φ' ((1 : Aq) ⊗ₜ h) := by
    simp [φ', Algebra.TensorProduct.lift_tmul]
  rw [h1, ← hΨev, ev_tmul, hi, red_apply, one_mul]
  rfl

end Ev

section Transport
variable (q : ℕ) [hq : Fact q.Prime] (Aq : ValuationSubring Qb) [hAq : Fact (Aq.LiesOverPrime q)]
variable (H : Type) [CommRing H] [HopfAlgebra (Zq q) H] [Module.Finite (Zq q) H]
variable {J : Type} [AddCommGroup J] (M : AddSubgroup J) (e : WithConv (Pt q H) ≃ ↥M)
  (he_add : ∀ f g, e (f * g) = e f + e g)

include he_add in
omit hq in
theorem e_one : e 1 = 0 := by
  have h := he_add 1 1
  rw [one_mul] at h
  simpa using h

include he_add in
omit hq in
theorem e_symm_add (x y : ↥M) : e.symm (x + y) = e.symm x * e.symm y :=
  e.injective (by rw [he_add]; simp)

include he_add in
omit hq in
theorem e_symm_zero : e.symm 0 = 1 := by
  rw [← e_one q H M e he_add, Equiv.symm_apply_apply]

def χ : Multiplicative ↥M →* WithConv (H →ₐ[Zq q] κ Aq) where
  toFun x := redHom q Aq H (e.symm x.toAdd)
  map_one' := by rw [toAdd_one, e_symm_zero q H M e he_add, map_one]
  map_mul' x y := by rw [toAdd_mul, e_symm_add q H M e he_add, map_mul]

def ψ : ↥M →+ Additive (WithConv (H →ₐ[Zq q] κ Aq))ˣ where
  toFun x := Additive.ofMul ((χ q Aq H M e he_add).toHomUnits (Multiplicative.ofAdd x))
  map_zero' := by simp
  map_add' x y := by rw [ofAdd_add, map_mul, ofMul_mul]

theorem ψ_apply_val (x : ↥M) :
    ((Additive.toMul (ψ q Aq H M e he_add x) : (WithConv (H →ₐ[Zq q] κ Aq))ˣ) :
      WithConv (H →ₐ[Zq q] κ Aq)) = toConv (red q Aq H (e.symm x).ofConv) := rfl

theorem ψ_eq_iff (x y : ↥M) :
    ψ q Aq H M e he_add x = ψ q Aq H M e he_add y ↔
      red q Aq H (e.symm x).ofConv = red q Aq H (e.symm y).ofConv := by
  constructor
  · intro h
    exact congrArg (fun u => ((Additive.toMul u : (WithConv (H →ₐ[Zq q] κ Aq))ˣ) :
      WithConv (H →ₐ[Zq q] κ Aq)).ofConv) h
  · intro h
    apply Additive.toMul.injective
    apply Units.ext
    rw [ψ_apply_val, ψ_apply_val, h]

theorem mem_ker_iff (x : ↥M) :
    x ∈ (ψ q Aq H M e he_add).ker ↔
      red q Aq H (e.symm x).ofConv = (1 : WithConv (H →ₐ[Zq q] κ Aq)).ofConv := by
  rw [AddMonoidHom.mem_ker, ← map_zero (ψ q Aq H M e he_add), ψ_eq_iff, e_symm_zero q H M e he_add, red_one]

def K₀ : AddSubgroup ↥M := (ψ q Aq H M e he_add).ker

def K : AddSubgroup J := (K₀ q Aq H M e he_add).map M.subtype

theorem K_le : K q Aq H M e he_add ≤ M := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

theorem coe_mem_K_iff (x : ↥M) : (x : J) ∈ K q Aq H M e he_add ↔ x ∈ K₀ q Aq H M e he_add := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.coe_injective hyx]
  · intro hx; exact ⟨x, hx, rfl⟩

theorem K_addSubgroupOf : (K q Aq H M e he_add).addSubgroupOf M = K₀ q Aq H M e he_add :=
  AddSubgroup.comap_map_eq_self_of_injective (f := M.subtype) Subtype.coe_injective _

theorem mem_K_iff (f : WithConv (Pt q H)) :
    ((e f : ↥M) : J) ∈ K q Aq H M e he_add ↔
      ∀ h : H, Aq.valuation (f h - algebraMap (Zq q) Qb (Coalgebra.counit h)) < 1 := by
  rw [coe_mem_K_iff, K₀, mem_ker_iff, Equiv.symm_apply_apply, red_eq_one_iff]

variable [DistribMulAction (Qb ≃ₐ[ℚ] Qb) J]
  (he_act : ∀ (σ : Qb ≃ₐ[ℚ] Qb) (f g : WithConv (Pt q H)),
    (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))

include he_act in

theorem inertia_mem_K (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ Aq.inertiaSubgroupIn ℚ) (x : J) (hx : x ∈ M) :
    σ • x - x ∈ K q Aq H M e he_add := by
  set f : WithConv (Pt q H) := e.symm ⟨x, hx⟩ with hf
  let g : WithConv (Pt q H) := toConv (galPt q H σ f.ofConv)
  have hfx : ((e f : ↥M) : J) = x := by rw [hf, Equiv.apply_symm_apply]
  have hgx : ((e g : ↥M) : J) = σ • x := by rw [← hfx]; exact he_act σ f g (fun h => rfl)
  rw [← hgx, ← hfx, show ((e g : ↥M) : J) - ((e f : ↥M) : J) = ((e g - e f : ↥M) : J) from rfl,
    coe_mem_K_iff, K₀, AddMonoidHom.sub_mem_ker_iff, ψ_eq_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact red_galPt q Aq H σ hσ f.ofConv

end Transport

section Count
variable (q : ℕ) [hq : Fact q.Prime] (Aq : ValuationSubring Qb) [hAq : Fact (Aq.LiesOverPrime q)]
variable (H : Type) [CommRing H] [HopfAlgebra (Zq q) H] [Module.Finite (Zq q) H] [Module.Flat (Zq q) H]
  [Coalgebra.IsCocomm (Zq q) H]
variable {J : Type} [AddCommGroup J] (M : AddSubgroup J) (e : WithConv (Pt q H) ≃ ↥M)
  (he_add : ∀ f g, e (f * g) = e f + e g)

theorem natCard_quot (hκ : IsAlgClosed (κ Aq)) :
    Nat.card (↥M ⧸ K₀ q Aq H M e he_add) = Nat.card (H →ₐ[Zq q] κ Aq) := by
  rw [K₀, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (ψ q Aq H M e he_add)).toEquiv]
  let F : ↥(ψ q Aq H M e he_add).range → (H →ₐ[Zq q] κ Aq) := fun u =>
    ((Additive.toMul (u : Additive (WithConv (H →ₐ[Zq q] κ Aq))ˣ) : (WithConv (H →ₐ[Zq q] κ Aq))ˣ) :
      WithConv (H →ₐ[Zq q] κ Aq)).ofConv
  apply Nat.card_eq_of_bijective F
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    exact Subtype.ext (Additive.toMul.injective (Units.ext (ofConv_injective h)))
  · intro φ
    obtain ⟨f, hf⟩ := red_surjective q Aq H hκ φ
    refine ⟨⟨ψ q Aq H M e he_add (e (toConv f)), ⟨_, rfl⟩⟩, ?_⟩
    show (toConv (red q Aq H (e.symm (e (toConv f))).ofConv)).ofConv = φ
    rw [Equiv.symm_apply_apply]; exact hf

def algHomEquivRingHom (S : Type) [CommRing S] [Algebra (Zq q) S] : (H →ₐ[Zq q] S) ≃ (H →+* S) where
  toFun f := f.toRingHom
  invFun g :=
    { g with
      commutes' := fun r =>
        RingHom.congr_fun (ringHom_Zq_ext q (g.comp (algebraMap (Zq q) H)) (algebraMap (Zq q) S)) r }
  left_inv f := AlgHom.ext fun _ => rfl
  right_inv g := RingHom.ext fun _ => rfl

omit hq in

def ringHomCongr {S T : Type} [CommRing S] [CommRing T] (ε : S ≃+* T) : (H →+* S) ≃ (H →+* T) where
  toFun g := ε.toRingHom.comp g
  invFun g := ε.symm.toRingHom.comp g
  left_inv g := RingHom.ext fun x => by simp
  right_inv g := RingHom.ext fun x => by simp

end Count

end H140
p2m_reactivate "P2MW.S_GaloisRep_exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf.H140"

theorem solution
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    ∃ K : AddSubgroup J, K ≤ M ∧
      (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
        ((e f : ↥M) : J) ∈ K ↔
          ∀ h : H, Aq.valuation (f h
            - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) ∧
      (∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ K) ∧
      Nat.card (↥M ⧸ K.addSubgroupOf M) = Nat.card (H →+* AlgebraicClosure (ZMod q)) := by
  classical
  haveI : Fact (Aq.LiesOverPrime q) := ⟨hAq⟩
  obtain ⟨ε⟩ :=
    ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime Aq hAq
  have hκ : IsAlgClosed (H140.κ Aq) := IsAlgClosed.of_ringEquiv (AlgebraicClosure (ZMod q)) (H140.κ Aq) ε.symm
  refine ⟨H140.K q Aq H M e he_add, H140.K_le q Aq H M e he_add, fun f => H140.mem_K_iff q Aq H M e he_add f,
    fun σ hσ x hx => H140.inertia_mem_K q Aq H M e he_add he_act σ hσ x hx, ?_⟩
  rw [H140.K_addSubgroupOf, H140.natCard_quot q Aq H M e he_add hκ,
    Nat.card_congr (H140.algHomEquivRingHom q H (H140.κ Aq)), Nat.card_congr (H140.ringHomCongr H ε)]

end
end S_GaloisRep_exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf
end P2MW
export P2MW.S_GaloisRep_exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf (solution)
