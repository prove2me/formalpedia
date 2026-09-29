-- Prove2me | solution 1 for CuspidalType.charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1e3669c3-ba52-5147-ac65-a538fb643a84

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff

set_option autoImplicit false

set_option linter.unusedVariables false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff.CuspidalType"

open Polynomial

namespace CuspidalType
p2m_export "CuspidalType" "GL2 ProjLine ind quadBasis torus charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow"
namespace CycChar
p2m_open "CuspidalType"

theorem periodic_mul {R : Type*} (f : ℕ → R) (m : ℕ) (hf : ∀ j, f (j + m) = f j) (j t : ℕ) :
    f (j + m * t) = f j := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, hf, ih]

theorem prod_range_mul_of_periodic {R : Type*} [CommMonoid R] (f : ℕ → R) (m : ℕ)
    (hf : ∀ j, f (j + m) = f j) (t : ℕ) :
    ∏ j ∈ Finset.range (m * t), f j = (∏ i ∈ Finset.range m, f i) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, pow_succ]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [add_comm, periodic_mul f m hf i t]

theorem prod_range_X_sub_C_pow_eq {K : Type*} [CommRing K] [IsDomain K] {η : K} {m : ℕ} (hm : 0 < m)
    (hη : IsPrimitiveRoot η m) (t : ℕ) :
    ∏ j ∈ Finset.range (m * t), (X - C (η ^ j)) = (X ^ m - 1) ^ t := by
  rw [prod_range_mul_of_periodic (fun j => X - C (η ^ j)) m
    (fun j => by show X - C (η ^ (j + m)) = X - C (η ^ j); rw [pow_add, hη.pow_eq_one, mul_one]) t]
  congr 1
  rw [show (X ^ m - 1 : K[X]) = X ^ m - C 1 by rw [map_one], X_pow_sub_C_eq_prod hη hm (one_pow m)]
  simp only [mul_one]

section Cyclic

variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
variable {K : Type*} [Field K]

theorem prod_X_sub_C_apply_eq [Fintype (G →* Kˣ)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (Nat.card G)) (x : G) :
    ∏ χ : G →* Kˣ, (X - C ((χ x : Kˣ) : K)) = (X ^ orderOf x - 1) ^ (Nat.card G / orderOf x) := by
  classical
  have hN0 : 0 < Nat.card G := Nat.card_pos
  haveI : NeZero (Nat.card G) := ⟨hN0.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg

  obtain ⟨a, rfl⟩ : ∃ a : ℕ, g ^ a = x := by
    have := hg x
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at this

  have hζne : ζ ≠ 0 := hζ.ne_zero hN0.ne'
  let ζu : Kˣ := Units.mk0 ζ hζne
  have hζu : IsPrimitiveRoot ζu (Nat.card G) := by
    rw [← IsPrimitiveRoot.coe_units_iff]; exact hζ
  have hoζ : orderOf ζu = Nat.card G := hζu.eq_orderOf.symm
  have hdvd : ∀ j : ℕ, orderOf (ζu ^ j) ∣ orderOf g := fun j => by
    rw [hog, ← hoζ]; exact orderOf_pow_dvd j
  let χ : ℕ → (G →* Kˣ) := fun j => monoidHomOfForallMemZpowers hg (hdvd j)
  have hχg : ∀ j, χ j g = ζu ^ j := fun j => monoidHomOfForallMemZpowers_apply_gen hg (hdvd j)

  have hinj : Set.InjOn χ (Finset.range (Nat.card G) : Set ℕ) := by
    intro i hi j hj hij
    have := congrArg (fun φ : G →* Kˣ => φ g) hij
    simp only [hχg] at this
    exact hζu.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) this
  have himage : (Finset.range (Nat.card G)).image χ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro φ
    have hφ : (φ g) ^ Nat.card G = 1 := by rw [← map_pow, ← hog, pow_orderOf_eq_one, map_one]
    have hφ' : ((φ g : Kˣ) : K) ^ Nat.card G = 1 := by rw [← Units.val_pow_eq_pow_val, hφ, Units.val_one]
    obtain ⟨j, hj, hjφ⟩ := hζ.eq_pow_of_pow_eq_one hφ'
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
    refine (MonoidHom.eq_iff_eq_on_generator hg _ _).mpr ((hχg j).trans (Units.ext ?_))
    rw [Units.val_pow_eq_pow_val]; exact hjφ
  rw [← himage, Finset.prod_image hinj]

  have hval : ∀ j, (((χ j) (g ^ a) : Kˣ) : K) = (ζ ^ a) ^ j := fun j => by
    rw [map_pow, hχg, ← pow_mul, mul_comm, pow_mul]
    simp [ζu]
  simp_rw [hval]

  set m := orderOf (g ^ a) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hζfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card G, hN0, hζ.pow_eq_one⟩
  have hmη : orderOf (ζ ^ a) = m := by
    rw [hm, hζfin.orderOf_pow, orderOf_pow g, hog, ← hζ.eq_orderOf]
  have hη : IsPrimitiveRoot (ζ ^ a) m := hmη ▸ IsPrimitiveRoot.orderOf (ζ ^ a)
  have hmN : Nat.card G = m * (Nat.card G / m) := (Nat.mul_div_cancel' (hm ▸ orderOf_dvd_natCard (g ^ a))).symm
  conv_lhs => rw [hmN]
  exact prod_range_X_sub_C_pow_eq hm0 hη _

end Cyclic

end CuspidalType.CycChar

namespace CuspidalType
p2m_export "CuspidalType" "GL2 ProjLine ind quadBasis torus charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow"
namespace IndTorusChar
p2m_open "CuspidalType"

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff.CuspidalType"
open scoped Matrix

variable (q : ℕ) [Fact q.Prime]

theorem torus_mulVec_repr (β : (GaloisField q 2)ˣ) (w : GaloisField q 2) :
    ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ ⇑((quadBasis q).repr w) =
      ⇑((quadBasis q).repr ((β : GaloisField q 2) * w)) := by
  have hmat : ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      LinearMap.toMatrix (quadBasis q) (quadBasis q) (Algebra.lmul (ZMod q) (GaloisField q 2) (β : GaloisField q 2)) := rfl
  rw [hmat, LinearMap.toMatrix_mulVec_repr]
  rfl

theorem torus_smul_mk (β : (GaloisField q 2)ˣ) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    (torus q β) • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q) (((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v)
        (by
          intro h0
          have := congrArg (fun u => ((torus q β)⁻¹ : GL2 q).val *ᵥ u) h0
          simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
          rw [show ((torus q β)⁻¹ : GL2 q).val * ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 from
            Units.inv_mul _, Matrix.one_mulVec] at this
          exact hv this) := by
  change (Matrix.GeneralLinearGroup.toLin (torus q β)) • Projectivization.mk (ZMod q) v hv = _
  rw [Projectivization.smul_mk]
  congr 1

theorem exists_repr_eq (v : Fin 2 → ZMod q) : ∃ w : GaloisField q 2, ⇑((quadBasis q).repr w) = v := by
  refine ⟨(quadBasis q).equivFun.symm v, ?_⟩
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

noncomputable abbrev scalars : Subgroup (GaloisField q 2)ˣ := (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom).range

theorem forall_smul_eq_iff_mem_scalars (β : (GaloisField q 2)ˣ) :
    (∀ x : ProjLine q, (torus q β) • x = x) ↔ β ∈ scalars q := by
  constructor
  · intro h

    have h1 : ((quadBasis q).repr (1 : GaloisField q 2) : Fin 2 → ZMod q) ≠ 0 := by
      intro h0
      have : (quadBasis q).repr (1 : GaloisField q 2) = 0 := DFunLike.coe_injective h0
      exact one_ne_zero ((quadBasis q).repr.map_eq_zero_iff.mp this)
    have hx := h (Projectivization.mk (ZMod q) _ h1)
    rw [torus_smul_mk, Projectivization.mk_eq_mk_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [torus_mulVec_repr, mul_one] at ha
    have hβ : (β : GaloisField q 2) = algebraMap (ZMod q) (GaloisField q 2) (a : ZMod q) := by
      have h1' : ⇑((quadBasis q).repr ((a : ZMod q) • (1 : GaloisField q 2))) = ⇑((quadBasis q).repr (β : GaloisField q 2)) := by
        rw [map_smul]; ext i; (have h__af := congrFun ha i; simp at h__af; exact h__af)
      have h2 : (a : ZMod q) • (1 : GaloisField q 2) = (β : GaloisField q 2) :=
        (quadBasis q).repr.injective (DFunLike.coe_injective h1')
      rw [Algebra.smul_def, mul_one] at h2
      exact h2.symm
    refine MonoidHom.mem_range.mpr ⟨a, Units.ext ?_⟩
    simpa using hβ.symm
  · intro hmem y
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hmem
    induction y using Projectivization.ind with
    | h u hu =>
      rw [torus_smul_mk, Projectivization.mk_eq_mk_iff]
      obtain ⟨w', rfl⟩ := exists_repr_eq q u
      refine ⟨a, ?_⟩
      rw [torus_mulVec_repr]
      show a • ⇑((quadBasis q).repr w') = ⇑((quadBasis q).repr ((algebraMap (ZMod q) (GaloisField q 2) (a : ZMod q)) * w'))
      rw [← Algebra.smul_def, map_smul]
      ext i; simp [Units.smul_def]

theorem orderOf_toPermHom_torus (α : (GaloisField q 2)ˣ) :
    orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) =
      orderOf (QuotientGroup.mk (s := scalars q) α) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow, ← map_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← forall_smul_eq_iff_mem_scalars,
    Equiv.ext_iff]
  exact forall_congr' fun x => by rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]

theorem card_quotient_scalars : Nat.card ((GaloisField q 2)ˣ ⧸ scalars q) = q + 1 := by
  classical
  have hq : q.Prime := Fact.out
  have hT : Nat.card (GaloisField q 2)ˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, GaloisField.card q 2 two_ne_zero]
  have hinj : Function.Injective (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom) :=
    Units.map_injective (algebraMap (ZMod q) (GaloisField q 2)).injective
  have e : (ZMod q)ˣ ≃* scalars q := MonoidHom.ofInjective hinj
  have hZ : Nat.card (scalars q) = q - 1 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units]
  have h := (scalars q).card_eq_card_quotient_mul_card_subgroup
  rw [hT, hZ] at h
  have hq1 : 0 < q - 1 := by have := hq.two_le; omega
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have := hq.two_le
    zify [Nat.one_le_pow 2 q hq.pos, hq.one_lt.le]
    ring
  rw [hsq] at h
  exact (Nat.eq_of_mul_eq_mul_right hq1 h).symm

end CuspidalType.IndTorusChar

open Polynomial _root_.CuspidalType _root_.P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff.CuspidalType in
theorem solution
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (S : Finset ((GaloisField q 2)ˣ →* Kˣ))
    (hS : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1)
    (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) = ∏ μ ∈ S, (X - C ((μ α : Kˣ) : K)) := by
  classical
  open CuspidalType.IndTorusChar CuspidalType.CycChar in

  let Z : Subgroup (GaloisField q 2)ˣ := scalars q
  haveI : IsCyclic ((GaloisField q 2)ˣ ⧸ Z) := isCyclic_of_surjective _ (QuotientGroup.mk'_surjective Z)
  have hN : Nat.card ((GaloisField q 2)ˣ ⧸ Z) = q + 1 := card_quotient_scalars q
  haveI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩

  haveI : Fintype (((GaloisField q 2)ˣ ⧸ Z) →* Kˣ) := by
    haveI : HasEnoughRootsOfUnity K (Monoid.exponent ((GaloisField q 2)ˣ ⧸ Z)) := by
      rw [IsCyclic.exponent_eq_card, hN]; infer_instance
    exact Fintype.ofFinite _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := K) (n := q + 1)

  let infl : (((GaloisField q 2)ˣ ⧸ Z) →* Kˣ) → ((GaloisField q 2)ˣ →* Kˣ) := fun χ => χ.comp (QuotientGroup.mk' Z)
  have hinfl_inj : Function.Injective infl := by
    intro χ₁ χ₂ h
    ext y
    exact congrArg Units.val (DFunLike.congr_fun h y)
  have hS' : S = Finset.univ.image infl := by
    ext μ
    rw [hS, Finset.mem_image]
    constructor
    · intro hμ
      have hker : ∀ z ∈ Z, μ z = 1 := by
        intro z hz
        obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hz
        exact hμ c
      refine ⟨QuotientGroup.lift Z μ hker, Finset.mem_univ _, ?_⟩
      ext x; rfl
    · rintro ⟨χ, -, rfl⟩ c
      show χ (QuotientGroup.mk' Z _) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨c, rfl⟩), map_one]
  rw [hS', Finset.prod_image fun χ₁ _ χ₂ _ h => hinfl_inj h]

  have hprod := prod_X_sub_C_apply_eq (G := (GaloisField q 2)ˣ ⧸ Z) (K := K) (hN ▸ hζ) (QuotientGroup.mk α)
  rw [hN, ← orderOf_toPermHom_torus] at hprod
  rw [CuspidalType.charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow, ← hprod]
  rfl

end S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff
end P2MW
export P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff (solution)
