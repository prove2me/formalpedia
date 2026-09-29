-- Prove2me | solution 1 for CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/40b614c0-2df8-5e36-b838-f1f31010cf4f

import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Theorems.Thm_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place
import Theorems.Thm_CerednikDrinfeld_HeckeTower_atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero
import Theorems.Thm_CerednikDrinfeld_HeckeTower_smul_phi_eq_phi_smul_of_descentIntertwining_one_zero
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_projGenLinGroup_mk_unitsMap_eq_one_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

section
open CerednikDrinfeld.Mumford AlgebraicCurve

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder classSetShift levelHeckeUSet ClassSetHeckeLaws CosetGraph.Loc CosetGraph.toLoc CosetGraph.awayUnits DescentIntertwining HeckeTower.AwayPrime HeckeTower.Obj HeckeTower.Arr HeckeTower.dom HeckeTower.cod HeckeTower.TowerData Mumford.frac_smul_def Mumford.frac_smul_algebraMap Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.AmbientSemilinearAut Mumford.AmbientSemilinearAut.fracMap Omega.PseudoUniformizer Omega.IsometricAut Omega.HolRingOf Omega.HolRingOf.smul_def Omega.toAmbientOf Omega.toAmbientOfHom Mumford.mem_map_conj_iff CosetGraph.atkinLehner_relations_levelGroups_place HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf"
namespace OmegaSigma
p2m_open "CerednikDrinfeld"

theorem zmod2_eq_of_ne_one_of_ne_one : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by
  decide

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
  [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]

theorem coe_galC_pow_smul {S : Type} [Group S] (Δ : Subgroup G)
    (galC : S →* SemilinearAut K ↥(invariantFieldOf K G M Δ)) (σ : S) (g : G)
    (h : ∀ y : ↥(invariantFieldOf K G M Δ), ((galC σ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = g • (y : FractionRing M)) :
    ∀ (u : ℕ) (y : ↥(invariantFieldOf K G M Δ)),
      ((galC (σ ^ u) • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = (g ^ u) • (y : FractionRing M) := by
  intro u
  induction u with
  | zero => intro y; simp
  | succ u ih => intro y; rw [pow_succ, pow_succ, map_mul, mul_smul, mul_smul, ← h, ih]

theorem exists_decomposition
    {D : Type} [Group D] (amb : D →* AmbientSemilinearAut K G M) (χ : D →* Multiplicative (ZMod 2))
    {S : Type} [Group S] (scalar : S →* D) (ιS : D →* S) (σ₀ σ₁ : S) (χS : S →* Multiplicative (ZMod 2))
    (hP : ∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v)
    (hsc0 : scalar σ₀ = 1) (hsc1 : scalar σ₁ = 1) (hscι : ∀ τ, scalar (ιS τ) = τ)
    (hX1 : ∀ τ, χS (ιS τ) = χ τ) (hX3 : χS σ₁ = 1)
    (Δ : Subgroup G) (w wbar : G) (hw : w ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
    (hwbar : wbar ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
    (galC : S →* SemilinearAut K ↥(invariantFieldOf K G M Δ))
    (hGι : ∀ (τ : D) (y : ↥(invariantFieldOf K G M Δ)),
      ((galC (ιS τ) • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
        (if χ τ = 1 then (1 : G) else w) • AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M))
    (hG0 : ∀ y : ↥(invariantFieldOf K G M Δ), ((galC σ₀ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = w • (y : FractionRing M))
    (hG1 : ∀ y : ↥(invariantFieldOf K G M Δ), ((galC σ₁ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = wbar • (y : FractionRing M)) :
    ∀ σ : S, ∃ (τ : D) (u v : ℕ),
      σ = ιS τ * σ₀ ^ u * σ₁ ^ v ∧ scalar σ = τ ∧
      ((if χ τ = 1 then (1 : G) else w) * w ^ u * wbar ^ v) ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G) ∧
      χS σ = χ τ * χS σ₀ ^ u ∧
      ∀ y : ↥(invariantFieldOf K G M Δ),
        ((galC σ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
          ((if χ τ = 1 then (1 : G) else w) * w ^ u * wbar ^ v) •
            AmbientSemilinearAut.fracMap (amb (scalar σ)) (y : FractionRing M) := by
  intro σ
  obtain ⟨τ, u, v, rfl⟩ := hP σ
  have hsc : scalar (ιS τ * σ₀ ^ u * σ₁ ^ v) = τ := by
    rw [map_mul, map_mul, map_pow, map_pow, hscι, hsc0, hsc1, one_pow, one_pow, mul_one, mul_one]
  refine ⟨τ, u, v, rfl, hsc, ?_, ?_, ?_⟩
  ·
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ hw u)) (Subgroup.pow_mem _ hwbar v)
    split_ifs
    · exact Subgroup.one_mem _
    · exact hw
  ·
    rw [map_mul, map_mul, map_pow, map_pow, hX1, hX3, one_pow, mul_one]
  · intro y
    rw [hsc, map_mul, map_mul, mul_smul, mul_smul, hGι,
      coe_galC_pow_smul K G M Δ galC σ₀ w hG0 u, coe_galC_pow_smul K G M Δ galC σ₁ wbar hG1 v,
      AmbientSemilinearAut.fracMap_smul, AmbientSemilinearAut.fracMap_smul, mul_smul, mul_smul]

theorem chiS_eq_of_decomposition
    {D : Type} [Group D] (χ : D →* Multiplicative (ZMod 2))
    {S : Type} [Group S] (ιS : D →* S) (σ₀ σ₁ : S) (χS : S →* Multiplicative (ZMod 2))
    (hX1 : ∀ τ, χS (ιS τ) = χ τ) (hX2 : χS σ₀ ≠ 1) (hX3 : χS σ₁ = 1)
    (ν : G →* Multiplicative (ZMod 2)) (w wbar : G) (hνw : ν w ≠ 1) (hνwbar : ν wbar = 1)
    (τ : D) (u v : ℕ) :
    χS (ιS τ * σ₀ ^ u * σ₁ ^ v) = ν ((if χ τ = 1 then (1 : G) else w) * w ^ u * wbar ^ v) := by
  rw [map_mul, map_mul, map_pow, map_pow, hX1, hX3, one_pow, mul_one,
    map_mul, map_mul, map_pow, map_pow, hνwbar, one_pow, mul_one,
    zmod2_eq_of_ne_one_of_ne_one (χS σ₀) (ν w) hX2 hνw]
  split_ifs with h
  · rw [h, map_one]
  · rw [zmod2_eq_of_ne_one_of_ne_one (χ τ) (ν w) h hνw]

end Generic

section NormParity

open Quaternion QuaternionAlgebra

variable {a b : ℚ}

theorem nrd_units_ne_zero (x : (ℍ[ℚ, a, b])ˣ) : nrd (x : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have h1 := QuaternionAlgebra.nrd_mul (x : ℍ[ℚ, a, b]) ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  rw [Units.mul_inv, nrd_one, h, zero_mul] at h1
  exact one_ne_zero h1

noncomputable def normParity (r : ℕ) [Fact r.Prime] : (ℍ[ℚ, a, b])ˣ →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (((padicValRat r (nrd (x : ℍ[ℚ, a, b])) : ℤ) : ZMod 2))
  map_one' := by simp only [Units.val_one, nrd_one, padicValRat.one, Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    simp only [Units.val_mul, QuaternionAlgebra.nrd_mul]
    rw [padicValRat.mul (nrd_units_ne_zero _) (nrd_units_ne_zero _), Int.cast_add, ofAdd_add]

theorem normParity_apply (r : ℕ) [Fact r.Prime] (x : (ℍ[ℚ, a, b])ˣ) :
    normParity r x = Multiplicative.ofAdd (((padicValRat r (nrd (x : ℍ[ℚ, a, b])) : ℤ) : ZMod 2)) := rfl

theorem normParity_eq_one_iff (r : ℕ) [Fact r.Prime] (x : (ℍ[ℚ, a, b])ˣ) :
    normParity r x = 1 ↔ Even (padicValRat r (nrd (x : ℍ[ℚ, a, b]))) := by
  rw [normParity_apply, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat, even_iff_two_dvd]

theorem normParity_ne_one_of_nrd_eq (r : ℕ) [Fact r.Prime] (x : (ℍ[ℚ, a, b])ˣ) (hx : nrd (x : ℍ[ℚ, a, b]) = (r : ℚ)) :
    normParity r x ≠ 1 := by
  rw [Ne, normParity_eq_one_iff, hx]
  have : padicValRat r (r : ℚ) = 1 := by exact_mod_cast padicValRat.self (Fact.out : r.Prime).one_lt
  rw [this]; decide

theorem normParity_eq_one_of_nrd_eq (r r' : ℕ) [Fact r.Prime] [Fact r'.Prime] (hrr : r' ≠ r) (x : (ℍ[ℚ, a, b])ˣ)
    (hx : nrd (x : ℍ[ℚ, a, b]) = (r' : ℚ)) : normParity r x = 1 := by
  rw [normParity_eq_one_iff, hx]
  have : padicValRat r (r' : ℚ) = 0 := by
    rw [show ((r' : ℚ)) = ((r' : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast padicValNat_primes hrr.symm
  rw [this]; exact ⟨0, rfl⟩

end NormParity

end CerednikDrinfeld.OmegaSigma
end

section
open CerednikDrinfeld.Mumford AlgebraicCurve

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder classSetShift levelHeckeUSet ClassSetHeckeLaws CosetGraph.Loc CosetGraph.toLoc CosetGraph.awayUnits DescentIntertwining HeckeTower.AwayPrime HeckeTower.Obj HeckeTower.Arr HeckeTower.dom HeckeTower.cod HeckeTower.TowerData Mumford.frac_smul_def Mumford.frac_smul_algebraMap Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.AmbientSemilinearAut Mumford.AmbientSemilinearAut.fracMap Omega.PseudoUniformizer Omega.IsometricAut Omega.HolRingOf Omega.HolRingOf.smul_def Omega.toAmbientOf Omega.toAmbientOfHom Mumford.mem_map_conj_iff CosetGraph.atkinLehner_relations_levelGroups_place HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf"
namespace OmegaExt
p2m_open "CerednikDrinfeld"

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
  [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]

theorem coe_galC_smul_eq_of_generators
    {D : Type} [Group D] (amb : D →* AmbientSemilinearAut K G M) (χ : D →* Multiplicative (ZMod 2))
    {S : Type} [Group S] (ιS : D →* S) (σ₀ σ₁ : S)
    (hP : ∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v)
    (Δ : Subgroup G) (w wbar : G)
    (galC : S →* SemilinearAut K ↥(invariantFieldOf K G M Δ))
    (hGι : ∀ (τ : D) (y : ↥(invariantFieldOf K G M Δ)),
      ((galC (ιS τ) • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
        (if χ τ = 1 then (1 : G) else w) • AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M))
    (hG0 : ∀ y : ↥(invariantFieldOf K G M Δ), ((galC σ₀ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = w • (y : FractionRing M))
    (hG1 : ∀ y : ↥(invariantFieldOf K G M Δ), ((galC σ₁ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = wbar • (y : FractionRing M))
    {k F : Type} [Field k] [Field F] [Algebra k F] (galF : S →* SemilinearAut k F) (ι : F →+* FractionRing M)
    (hιτ : ∀ (τ : D) (x : F), ι (galF (ιS τ) • x) = (if χ τ = 1 then (1 : G) else w) • AmbientSemilinearAut.fracMap (amb τ) (ι x))
    (hι₀ : ∀ x : F, ι (galF σ₀ • x) = w • ι x)
    (hι₁ : ∀ x : F, ι (galF σ₁ • x) = wbar • ι x) :
    ∀ (σ : S) (x : F) (y : ↥(invariantFieldOf K G M Δ)), (y : FractionRing M) = ι x →
      ((galC σ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = ι (galF σ • x) := by

  let E : S → Prop := fun σ => ∀ (x : F) (y : ↥(invariantFieldOf K G M Δ)), (y : FractionRing M) = ι x →
    ((galC σ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = ι (galF σ • x)
  have hE_one : E 1 := fun x y h => by simpa using h
  have hE_mul : ∀ a b : S, E a → E b → E (a * b) := fun a b ha hb x y h => by
    rw [map_mul, map_mul, mul_smul, mul_smul]
    exact ha _ _ (hb x y h)
  have hE_pow : ∀ (a : S) (n : ℕ), E a → E (a ^ n) := fun a n ha => by
    induction n with
    | zero => simpa using hE_one
    | succ n ih => rw [pow_succ]; exact hE_mul _ _ ih ha
  have hE_ι : ∀ τ : D, E (ιS τ) := fun τ x y h => by rw [hGι, h, hιτ]
  have hE_0 : E σ₀ := fun x y h => by rw [hG0, h, hι₀]
  have hE_1 : E σ₁ := fun x y h => by rw [hG1, h, hι₁]
  intro σ
  obtain ⟨τ, u, v, rfl⟩ := hP σ
  exact hE_mul _ _ (hE_mul _ _ (hE_ι τ) (hE_pow _ _ hE_0)) (hE_pow _ _ hE_1)

end CerednikDrinfeld.OmegaExt
end

section
open CerednikDrinfeld.Mumford AlgebraicCurve

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder classSetShift levelHeckeUSet ClassSetHeckeLaws CosetGraph.Loc CosetGraph.toLoc CosetGraph.awayUnits DescentIntertwining HeckeTower.AwayPrime HeckeTower.Obj HeckeTower.Arr HeckeTower.dom HeckeTower.cod HeckeTower.TowerData Mumford.frac_smul_def Mumford.frac_smul_algebraMap Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.AmbientSemilinearAut Mumford.AmbientSemilinearAut.fracMap Omega.PseudoUniformizer Omega.IsometricAut Omega.HolRingOf Omega.HolRingOf.smul_def Omega.toAmbientOf Omega.toAmbientOfHom Mumford.mem_map_conj_iff CosetGraph.atkinLehner_relations_levelGroups_place HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf"
namespace OmegaGen
p2m_open "CerednikDrinfeld"

theorem smul_map_eq_map_smul_of_generators
    {D S : Type} [Group D] [Group S] (ιS : D →* S) (σ₀ σ₁ : S)
    (hP : ∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v)
    {k Fc Fd : Type} [Field k] [Field Fc] [Field Fd] [Algebra k Fc] [Algebra k Fd]
    (Gc : S →* SemilinearAut k Fc) (Gd : S →* SemilinearAut k Fd) (φ : Fc → Fd)
    (hτ : ∀ (τ : D) (x : Fc), Gd (ιS τ) • φ x = φ (Gc (ιS τ) • x))
    (h0 : ∀ x : Fc, Gd σ₀ • φ x = φ (Gc σ₀ • x)) (h1 : ∀ x : Fc, Gd σ₁ • φ x = φ (Gc σ₁ • x)) :
    ∀ (σ : S) (x : Fc), Gd σ • φ x = φ (Gc σ • x) := by
  let E : S → Prop := fun σ => ∀ x : Fc, Gd σ • φ x = φ (Gc σ • x)
  have hE_one : E 1 := fun x => by simp
  have hE_mul : ∀ a b : S, E a → E b → E (a * b) := fun a b ha hb x => by
    rw [map_mul, map_mul, mul_smul, mul_smul, hb, ha]
  have hE_pow : ∀ (a : S) (n : ℕ), E a → E (a ^ n) := fun a n ha => by
    induction n with
    | zero => simpa using hE_one
    | succ n ih => rw [pow_succ]; exact hE_mul _ _ ih ha
  intro σ
  obtain ⟨τ, u, v, rfl⟩ := hP σ
  exact hE_mul _ _ (hE_mul _ _ (hτ τ) (hE_pow _ _ h0)) (hE_pow _ _ h1)

theorem baseAut_eq_of_generators
    {D S : Type} [Group D] [Group S] (ιS : D →* S) (σ₀ σ₁ : S)
    (hP : ∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v)
    (scalar : S →* D) (hscι : ∀ τ, scalar (ιS τ) = τ) (hsc0 : scalar σ₀ = 1) (hsc1 : scalar σ₁ = 1)
    {k F : Type} [Field k] [Field F] [Algebra k F] (Gal : S →* SemilinearAut k F) (base : D →* (k ≃+* k))
    (hτ : ∀ τ : D, SemilinearAut.baseAut (Gal (ιS τ)) = base τ)
    (h0 : SemilinearAut.baseAut (Gal σ₀) = 1) (h1 : SemilinearAut.baseAut (Gal σ₁) = 1) :
    ∀ σ : S, SemilinearAut.baseAut (Gal σ) = base (scalar σ) := by
  let E : S → Prop := fun σ => SemilinearAut.baseAut (Gal σ) = base (scalar σ)
  have hE_mul : ∀ a b : S, E a → E b → E (a * b) := fun a b ha hb => by
    show SemilinearAut.baseAut (Gal (a * b)) = base (scalar (a * b))
    rw [map_mul, map_mul, map_mul, SemilinearAut.baseAut_mul, ha, hb]
  have hE_one : E 1 := by
    show SemilinearAut.baseAut (Gal 1) = base (scalar 1)
    rw [map_one, map_one, map_one, SemilinearAut.baseAut_one]
  have hE_pow : ∀ (a : S) (n : ℕ), E a → E (a ^ n) := fun a n ha => by
    induction n with
    | zero => simpa using hE_one
    | succ n ih => rw [pow_succ]; exact hE_mul _ _ ih ha
  have hE0 : E σ₀ := by show SemilinearAut.baseAut (Gal σ₀) = base (scalar σ₀); rw [h0, hsc0, map_one]
  have hE1 : E σ₁ := by show SemilinearAut.baseAut (Gal σ₁) = base (scalar σ₁); rw [h1, hsc1, map_one]
  intro σ
  obtain ⟨τ, u, v, rfl⟩ := hP σ
  exact hE_mul _ _ (hE_mul _ _ (by show E (ιS τ); rw [show E (ιS τ) ↔ _ from Iff.rfl]; exact (hτ τ).trans (by rw [hscι]))
    (hE_pow _ _ hE0)) (hE_pow _ _ hE1)

section M1

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
  [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]

theorem mul_smul_eq_mul_smul_of_commutator_mem (Δ : Subgroup G) (w wbar : G)
    (hw : w ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G)) (hwbar : wbar ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
    (hc : w * wbar * w⁻¹ * wbar⁻¹ ∈ Δ) :
    ∀ x ∈ invariantFieldOf K G M Δ, (w * wbar) • x = (wbar * w) • x := by
  intro x hx
  have hmem : (wbar * w) • x ∈ invariantFieldOf K G M Δ := by
    rw [mul_smul]
    exact smul_mem_invariantFieldOf_of_mem_normalizer K G M Δ hwbar (smul_mem_invariantFieldOf_of_mem_normalizer K G M Δ hw hx)
  have hfix := (mem_invariantFieldOf_iff K G M Δ _).1 hmem _ hc
  calc (w * wbar) • x = (w * wbar * w⁻¹ * wbar⁻¹ * (wbar * w)) • x := by congr 1; group
    _ = (w * wbar * w⁻¹ * wbar⁻¹) • ((wbar * w) • x) := by rw [mul_smul]
    _ = (wbar * w) • x := hfix

end M1

end CerednikDrinfeld.OmegaGen
end

section
open CerednikDrinfeld.Mumford AlgebraicCurve

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder classSetShift levelHeckeUSet ClassSetHeckeLaws CosetGraph.Loc CosetGraph.toLoc CosetGraph.awayUnits DescentIntertwining HeckeTower.AwayPrime HeckeTower.Obj HeckeTower.Arr HeckeTower.dom HeckeTower.cod HeckeTower.TowerData Mumford.frac_smul_def Mumford.frac_smul_algebraMap Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.AmbientSemilinearAut Mumford.AmbientSemilinearAut.fracMap Omega.PseudoUniformizer Omega.IsometricAut Omega.HolRingOf Omega.HolRingOf.smul_def Omega.toAmbientOf Omega.toAmbientOfHom Mumford.mem_map_conj_iff CosetGraph.atkinLehner_relations_levelGroups_place HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf"
namespace OmegaArr
p2m_open "CerednikDrinfeld"

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
  [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]

theorem smul_smul_eq_of_mem (Γc : Subgroup G) (g nd nc : G)
    (hnc : nc ∈ Subgroup.normalizer ((Γc : Subgroup G) : Set G)) (hc : g⁻¹ * nd * g * nc⁻¹ ∈ Γc)
    (z : FractionRing M) (hz : z ∈ invariantFieldOf K G M Γc) : nd • (g • z) = g • (nc • z) := by
  have hmem : nc • z ∈ invariantFieldOf K G M Γc := smul_mem_invariantFieldOf_of_mem_normalizer K G M Γc hnc hz
  have hfix : (g⁻¹ * nd * g * nc⁻¹) • (nc • z) = nc • z := (mem_invariantFieldOf_iff K G M Γc _).1 hmem _ hc
  calc nd • (g • z) = (g * (g⁻¹ * nd * g * nc⁻¹) * nc) • z := by rw [← mul_smul]; congr 1; group
    _ = g • ((g⁻¹ * nd * g * nc⁻¹) • (nc • z)) := by rw [mul_smul, mul_smul]
    _ = g • (nc • z) := by rw [hfix]

theorem smul_algHom_eq_algHom_smul_of_generators
    {D : Type} [Group D] (amb : D →* AmbientSemilinearAut K G M) (χ : D →* Multiplicative (ZMod 2))
    {S : Type} [Group S] (ιS : D →* S) (σ₀ σ₁ : S)
    (hP : ∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v)
    (Γc Γd : Subgroup G) (wc wbc wd wbd : G)
    (galCc : S →* SemilinearAut K ↥(invariantFieldOf K G M Γc))
    (galCd : S →* SemilinearAut K ↥(invariantFieldOf K G M Γd))
    (hGιc : ∀ (τ : D) (y : ↥(invariantFieldOf K G M Γc)),
      ((galCc (ιS τ) • y : ↥(invariantFieldOf K G M Γc)) : FractionRing M) =
        (if χ τ = 1 then (1 : G) else wc) • AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M))
    (hG0c : ∀ y : ↥(invariantFieldOf K G M Γc), ((galCc σ₀ • y : ↥(invariantFieldOf K G M Γc)) : FractionRing M) = wc • (y : FractionRing M))
    (hG1c : ∀ y : ↥(invariantFieldOf K G M Γc), ((galCc σ₁ • y : ↥(invariantFieldOf K G M Γc)) : FractionRing M) = wbc • (y : FractionRing M))
    (hGιd : ∀ (τ : D) (y : ↥(invariantFieldOf K G M Γd)),
      ((galCd (ιS τ) • y : ↥(invariantFieldOf K G M Γd)) : FractionRing M) =
        (if χ τ = 1 then (1 : G) else wd) • AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M))
    (hG0d : ∀ y : ↥(invariantFieldOf K G M Γd), ((galCd σ₀ • y : ↥(invariantFieldOf K G M Γd)) : FractionRing M) = wd • (y : FractionRing M))
    (hG1d : ∀ y : ↥(invariantFieldOf K G M Γd), ((galCd σ₁ • y : ↥(invariantFieldOf K G M Γd)) : FractionRing M) = wbd • (y : FractionRing M))
    (g : G) (φ : ↥(invariantFieldOf K G M Γc) →ₐ[K] ↥(invariantFieldOf K G M Γd))
    (hφ : ∀ x : ↥(invariantFieldOf K G M Γc), (φ x : FractionRing M) = g • (x : FractionRing M))
    (hnc0 : wc ∈ Subgroup.normalizer ((Γc : Subgroup G) : Set G)) (hnc1 : wbc ∈ Subgroup.normalizer ((Γc : Subgroup G) : Set G))
    (h0 : g⁻¹ * wd * g * wc⁻¹ ∈ Γc) (h1 : g⁻¹ * wbd * g * wbc⁻¹ ∈ Γc) :
    ∀ (σ : S) (x : ↥(invariantFieldOf K G M Γc)), galCd σ • φ x = φ (galCc σ • x) := by
  let A : S → Prop := fun σ => ∀ x : ↥(invariantFieldOf K G M Γc), galCd σ • φ x = φ (galCc σ • x)
  have hA_one : A 1 := fun x => by simp
  have hA_mul : ∀ a b : S, A a → A b → A (a * b) := fun a b ha hb x => by
    rw [map_mul, map_mul, mul_smul, mul_smul, hb, ha]
  have hA_pow : ∀ (a : S) (n : ℕ), A a → A (a ^ n) := fun a n ha => by
    induction n with
    | zero => simpa using hA_one
    | succ n ih => rw [pow_succ]; exact hA_mul _ _ ih ha
  have hA0 : A σ₀ := fun x => Subtype.ext (by
    rw [hG0d, hφ, hφ, hG0c]
    exact smul_smul_eq_of_mem K G M Γc g wd wc hnc0 h0 _ x.2)
  have hA1 : A σ₁ := fun x => Subtype.ext (by
    rw [hG1d, hφ, hφ, hG1c]
    exact smul_smul_eq_of_mem K G M Γc g wbd wbc hnc1 h1 _ x.2)
  have hAι : ∀ τ : D, A (ιS τ) := fun τ x => Subtype.ext (by
    rw [hGιd, hφ, hφ, hGιc, AmbientSemilinearAut.fracMap_smul]
    have hz : AmbientSemilinearAut.fracMap (amb τ) (x : FractionRing M) ∈ invariantFieldOf K G M Γc := by
      rw [← AmbientSemilinearAut.coe_coeffActOf_toRingAut]; exact Subtype.mem _
    split_ifs with h
    · rw [one_smul, one_smul]
    · exact smul_smul_eq_of_mem K G M Γc g wd wc hnc0 h0 _ hz)
  intro σ
  obtain ⟨τ, u, v, rfl⟩ := hP σ
  exact hA_mul _ _ (hA_mul _ _ (hAι τ) (hA_pow _ _ hA0)) (hA_pow _ _ hA1)

end CerednikDrinfeld.OmegaArr
end

open scoped TensorProduct Quaternion NumberField MatrixGroups
p2m_open "IsDedekindDomain QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero.CerednikDrinfeld ModularCurve AlgebraicCurve"
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

namespace MKFunctSign

def zmod2Units : Multiplicative (ZMod 2) →* ℤˣ where
  toFun z := if z = 1 then 1 else -1
  map_one' := by simp
  map_mul' a b := by revert a b; decide
theorem zmod2Units_eq_one_iff (z : Multiplicative (ZMod 2)) : zmod2Units z = 1 ↔ z = 1 := by
  revert z; decide
end MKFunctSign

set_option maxHeartbeats 8000000 in
theorem solution

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁))
    (hI : CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁) :
∃ (S₁ : Type) (_ : Group S₁) (scalar₁ : S₁ →* ↥(A₁.decompositionSubgroup ℚ))
      (ιS₁ : ↥(A₁.decompositionSubgroup ℚ) →* S₁) (_ : ∀ τ, scalar₁ (ιS₁ τ) = τ)

      (σ₀₁ σ₁₁ : S₁)
      (χS₁ : S₁ →* Multiplicative (ZMod 2))

      (galF₁ : ∀ j : HeckeTower.Obj q q', S₁ →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j))

      (galFC₁ : ∀ j : HeckeTower.Obj q q',
        S₁ →* SemilinearAut A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)))

      (sgn₁ : S₁ →* ℤˣ),

      (∀ σ : S₁, ∃ (τ : ↥(A₁.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₁ τ * σ₀₁ ^ u * σ₁₁ ^ v) ∧
      scalar₁ σ₀₁ = 1 ∧ scalar₁ σ₁₁ = 1 ∧ σ₀₁ * σ₀₁ = 1 ∧ σ₁₁ * σ₁₁ = 1 ∧
      σ₀₁ * σ₁₁ = σ₁₁ * σ₀₁ ∧ (∀ τ, ιS₁ τ * σ₀₁ = σ₀₁ * ιS₁ τ) ∧ (∀ τ, ιS₁ τ * σ₁₁ = σ₁₁ * ιS₁ τ) ∧

      (∀ (H : Type) [Group H] (f : ↥(A₁.decompositionSubgroup ℚ) →* H) (h₀ h₂ : H),
        h₀ * h₀ = 1 → h₂ * h₂ = 1 → h₀ * h₂ = h₂ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₂ = h₂ * f τ) →
        ∃ F : S₁ →* H, (∀ τ, F (ιS₁ τ) = f τ) ∧ F σ₀₁ = h₀ ∧ F σ₁₁ = h₂) ∧

      (∀ j (σ : S₁) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (galF₁ j σ) a =
        ((scalar₁ σ : ↥(A₁.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), galF₁ none (ιS₁ τ) = galN τ) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₁.decompositionSubgroup ℚ)), galF₁ (some ℓ) (ιS₁ τ) = galT ℓ τ) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁) (x : 𝕋.objField (HeckeTower.cod α)),
        galF₁ (HeckeTower.dom α) σ • (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α x) =
          (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α (galF₁ (HeckeTower.cod α) σ • x))) ∧
      galF₁ none σ₀₁ = W 1 ∧ galF₁ none σ₁₁ = W 0 ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', galF₁ (some ℓ) σ₀₁ = WT ℓ 1 ∧ galF₁ (some ℓ) σ₁₁ = WT ℓ 0) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = χ₁ τ) ∧ χS₁ σ₀₁ ≠ 1 ∧ χS₁ σ₁₁ = 1 ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χS₁ (ιS₁ τ) = 1) ∧
      (∀ φ : ↥(A₁.decompositionSubgroup ℚ),
        A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χS₁ (ιS₁ φ) ≠ 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 ↔
        ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x) ∧

      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (scalar₁ σ) • c) ∧
      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (dIso₁ (scalar₁ σ)).toRingEquiv c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₀₁) c = c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₁₁) c = c) ∧
      (∀ j (σ : S₁) (x : 𝕋.objField j) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j x →
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j (galF₁ j σ • x)) ∧
      (∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j (ιS₁ τ) • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
          (if χ₁ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ j) •
            Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₀₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (w₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₁₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (wbar₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ (n : (ℍ[ℚ, a₂, b₂])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ t) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ n : (ℍ[ℚ, a₂, b₂])ˣ,
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧ (sgn₁ σ = 1 ↔ Even (padicValRat q' (nrd (n : ℍ[ℚ, a₂, b₂])))) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ (scalar₁ σ))) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 → sgn₁ (ιS₁ τ) = 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) ≠ 1 → sgn₁ (ιS₁ τ) = sgn₁ σ₀₁) ∧
      sgn₁ σ₀₁ = -1 ∧ sgn₁ σ₁₁ = 1 ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁)
        (φC : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.cod α))) →ₐ[A₁.valuation.Completion] ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.dom α)))),
        (∀ x, (φC x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (if α.2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ α.1) • (x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) →
        ∀ x, galFC₁ (HeckeTower.dom α) σ • φC x = φC (galFC₁ (HeckeTower.cod α) σ • x)) := by
  classical

  have hTA := CerednikDrinfeld.Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ↥(A₁.decompositionSubgroup ℚ)
      ((Omega.toAmbientOfHom ϖ₁ ρ₁).comp dIso₁) χ₁
  obtain ⟨S, hTA⟩ := hTA
  obtain ⟨instS, hTA⟩ := hTA
  obtain ⟨scalar, ιS, hscι, σ₀, σ₁, χS, hTA⟩ := hTA
  obtain ⟨hP, hsc0, hsc1, h00, h11, h01, hc0, hc1, hU, hX1, hX2, hX3, hA⟩ := hTA

  have hAL := CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place hN hqN hq'N hqq' hq5 hq'5 q' q hq'N hqN (Ne.symm hqq')
    hdef₂ Λ₂ R₂ hΛ₂ hR₂ hRΛ₂ n₂ hn₂ v₁ hv₁ s₁ sf₁ hs₁ Γ₁ hΓ₁0 hΓ₁ℓ w₁ wbar₁ hw₁ hwbar₁

  have hnorm : ∀ (j : HeckeTower.Obj q q') (g : (ℍ[ℚ, a₂, b₂])ˣ),
      (Γ₁ j).map (MulAut.conj g).toMonoidHom = Γ₁ j →
        g ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) := by
    intro j g hg
    rw [Subgroup.mem_normalizer_iff'']
    intro d
    rw [← Mumford.mem_map_conj_iff (ℍ[ℚ, a₂, b₂])ˣ g (Γ₁ j) d, hg]
  have hw : ∀ j, w₁ j ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) :=
    fun j => hnorm j _ (hAL j).1
  have hwbar : ∀ j, wbar₁ j ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) :=
    fun j => hnorm j _ (hAL j).2.1
  have hww : ∀ j, ∀ x ∈ Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j), (w₁ j * w₁ j) • x = x :=
    fun j x hx => (Mumford.mem_invariantFieldOf_iff _ _ _ (Γ₁ j) x).1 hx _ (hAL j).2.2.1

  have hscal : ∀ y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁), (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • y = y := by
    have hρc : ρ₁ (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) = 1 := by
      rw [hρ₁]
      have : Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ ↥(ValuationSubring.ratClosure A₁)).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) := by
        ext i k
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [this, Matrix.ProjGenLinGroup.mk_scalar]
    have hM : ∀ f : Omega.HolRingOf ϖ₁ ρ₁, (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • f = f := fun f => by
      rw [Omega.HolRingOf.smul_def, hρc, one_smul]
    intro y
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Omega.HolRingOf ϖ₁ ρ₁) y
    rw [← hab, Mumford.frac_smul_def, map_div₀, ← Mumford.frac_smul_def, ← Mumford.frac_smul_def,
      Mumford.frac_smul_algebraMap, Mumford.frac_smul_algebraMap, hM, hM]
  have hbb : ∀ j, ∀ x ∈ Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j), (wbar₁ j * wbar₁ j) • x = x := by
    intro j x hx
    have h5 := (hAL j).2.2.2.2.1
    have e : wbar₁ j * wbar₁ j = (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * ((Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)))⁻¹ * (wbar₁ j * wbar₁ j)) := by group
    rw [e, mul_smul, (Mumford.mem_invariantFieldOf_iff _ _ _ (Γ₁ j) x).1 hx _ h5, hscal]
  have hwb : ∀ j, ∀ x ∈ Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j), (w₁ j * wbar₁ j) • x = (wbar₁ j * w₁ j) • x :=
    fun j => CerednikDrinfeld.OmegaGen.mul_smul_eq_mul_smul_of_commutator_mem
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j) (w₁ j) (wbar₁ j) (hw j) (hwbar j) (hAL j).2.2.2.1
  have hAj := fun j => hA (Γ₁ j) (w₁ j) (wbar₁ j) (hw j) (hwbar j) (hww j) (hbb j) (hwb j)
  choose galFC hgalFC using hAj

  have hQ := CerednikDrinfeld.HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero hN hqN hq'N hqq' hq5 hq'5 hdef₂ Λ₂ R₂ hΛ₂ hR₂ hRΛ₂ n₂ hn₂ hS₂ hnorm₂ hsq₂ hlaws₂ A₁ hA₁ FN 𝕋 hfg galN galT hgalN hgalT W WT v₁ hv₁ ι₁ hι₁ ρ₁ hρ₁ ϖ₁ hϖ₁ s₁ sf₁ hs₁ Γ₁ hΓ₁0 hΓ₁ℓ w₁ wbar₁ hw₁ hwbar₁ dIso₁ hdIso₁ χ₁ ιM₁ hI
  obtain ⟨hWW, hW01, hGW, hWb, hWWT, hWT01, hGWT, hWTb⟩ := hQ
  have hF0 : ∃ F : S →* SemilinearAut (AlgebraicClosure ℚ) FN, (∀ τ, F (ιS τ) = galN τ) ∧ F σ₀ = W 1 ∧ F σ₁ = W 0 :=
    hU _ galN (W 1) (W 0) (hWW 1) (hWW 0) hW01 (fun τ => hGW τ 1) (fun τ => hGW τ 0)
  obtain ⟨F0, hF0ι, hF00, hF01⟩ := hF0
  have hFT : ∀ ℓ : HeckeTower.AwayPrime q q', ∃ F : S →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (∀ τ, F (ιS τ) = galT ℓ τ) ∧ F σ₀ = WT ℓ 1 ∧ F σ₁ = WT ℓ 0 :=
    fun ℓ => hU _ (galT ℓ) (WT ℓ 1) (WT ℓ 0) (hWWT ℓ 1) (hWWT ℓ 0) (hWT01 ℓ) (fun τ => hGWT ℓ τ 1) (fun τ => hGWT ℓ τ 0)
  choose FT hFT using hFT
  let galF : ∀ j : HeckeTower.Obj q q', S →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j) :=
    fun j => match j with
      | none => F0
      | some ℓ => FT ℓ

  have hIc := hI
  obtain ⟨hpar1, hpar2, hpar3, hI0a, hI0b, hI0c, hI1N, hI1T, hI2a, hI2b, hI2c, hI2d, hI3a, hI3b⟩ := hIc

  have hdec := fun j => CerednikDrinfeld.OmegaSigma.exists_decomposition
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((Omega.toAmbientOfHom ϖ₁ ρ₁).comp dIso₁) χ₁
      scalar ιS σ₀ σ₁ χS hP hsc0 hsc1 hscι hX1 hX3 (Γ₁ j) (w₁ j) (wbar₁ j) (hw j) (hwbar j) (galFC j)
      (hgalFC j).2.1 (hgalFC j).2.2.1 (hgalFC j).2.2.2
  have hnw : ∀ j : HeckeTower.Obj q q', nrd (w₁ j : ℍ[ℚ, a₂, b₂]) = (q' : ℚ) := fun j => by
    cases j with
    | none => exact hw₁.1.2
    | some ℓ => exact (hw₁.2 ℓ).2
  have hnb : ∀ j : HeckeTower.Obj q q', nrd (wbar₁ j : ℍ[ℚ, a₂, b₂]) = (q : ℚ) := fun j => by
    cases j with
    | none => exact hwbar₁.1.1
    | some ℓ => exact (hwbar₁.2 ℓ).1

  have hext0 := CerednikDrinfeld.OmegaExt.coe_galC_smul_eq_of_generators
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((Omega.toAmbientOfHom ϖ₁ ρ₁).comp dIso₁) χ₁
      ιS σ₀ σ₁ hP (Γ₁ none) (w₁ none) (wbar₁ none) (galFC none)
      (hgalFC none).2.1 (hgalFC none).2.2.1 (hgalFC none).2.2.2 F0 (ιM₁ none)
      (fun τ x => by rw [hF0ι]; exact hI1N τ x) (fun x => by rw [hF00]; exact hI2a x) (fun x => by rw [hF01]; exact hI2b x)
  have hextT := fun ℓ => CerednikDrinfeld.OmegaExt.coe_galC_smul_eq_of_generators
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((Omega.toAmbientOfHom ϖ₁ ρ₁).comp dIso₁) χ₁
      ιS σ₀ σ₁ hP (Γ₁ (some ℓ)) (w₁ (some ℓ)) (wbar₁ (some ℓ)) (galFC (some ℓ))
      (hgalFC (some ℓ)).2.1 (hgalFC (some ℓ)).2.2.1 (hgalFC (some ℓ)).2.2.2 (FT ℓ) (ιM₁ (some ℓ))
      (fun τ x => by rw [(hFT ℓ).1]; exact hI1T ℓ τ x) (fun x => by rw [(hFT ℓ).2.1]; exact hI2c ℓ x)
      (fun x => by rw [(hFT ℓ).2.2]; exact hI2d ℓ x)

  let baseD : ↥(A₁.decompositionSubgroup ℚ) →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :=
    { toFun := fun τ => ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hWb1 : ∀ i : Fin 2, SemilinearAut.baseAut (W i) = 1 := fun i => RingEquiv.ext (hWb i)
  have hWTb1 : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2), SemilinearAut.baseAut (WT ℓ i) = 1 :=
    fun ℓ i => RingEquiv.ext (hWTb ℓ i)
  have hbase0 := CerednikDrinfeld.OmegaGen.baseAut_eq_of_generators ιS σ₀ σ₁ hP scalar hscι hsc0 hsc1 F0 baseD
    (fun τ => by rw [hF0ι]; exact RingEquiv.ext (hgalN τ)) (by rw [hF00]; exact hWb1 1) (by rw [hF01]; exact hWb1 0)
  have hbaseT := fun ℓ => CerednikDrinfeld.OmegaGen.baseAut_eq_of_generators ιS σ₀ σ₁ hP scalar hscι hsc0 hsc1 (FT ℓ) baseD
    (fun τ => by rw [(hFT ℓ).1]; exact RingEquiv.ext (hgalT ℓ τ)) (by rw [(hFT ℓ).2.1]; exact hWTb1 ℓ 1)
    (by rw [(hFT ℓ).2.2]; exact hWTb1 ℓ 0)
  have hIP := CerednikDrinfeld.HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero hN hqN hq'N hqq' hq5 hq'5 hdef₂ Λ₂ R₂ hΛ₂ hR₂ hRΛ₂ n₂ hn₂ hS₂ hnorm₂ hsq₂ hlaws₂ A₁ hA₁ FN 𝕋 hfg galN galT hgalN hgalT W WT v₁ hv₁ ι₁ hι₁ ρ₁ hρ₁ ϖ₁ hϖ₁ s₁ sf₁ hs₁ Γ₁ hΓ₁0 hΓ₁ℓ w₁ wbar₁ hw₁ hwbar₁ dIso₁ hdIso₁ χ₁ ιM₁ hI
  obtain ⟨hIPgal, hIPW⟩ := hIP
  have harr := fun (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) =>
    CerednikDrinfeld.OmegaGen.smul_map_eq_map_smul_of_generators ιS σ₀ σ₁ hP F0 (FT ℓ) (fun x => 𝕋.φ (ℓ, i) x)
      (fun τ x => by rw [(hFT ℓ).1, hF0ι]; exact hIPgal ℓ i τ x)
      (fun x => by rw [(hFT ℓ).2.1, hF00]; exact hIPW ℓ i 1 x)
      (fun x => by rw [(hFT ℓ).2.2, hF01]; exact hIPW ℓ i 0 x)

  refine ⟨S, instS, scalar, ιS, hscι, σ₀, σ₁, χS, galF, galFC, (MKFunctSign.zmod2Units).comp χS,
    hP, hsc0, hsc1, h00, h11, h01, hc0, hc1, hU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hX1, hX2, hX3, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro j σ a
    cases j with
    | none => exact congrArg (fun e : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ => e a) (hbase0 σ)
    | some ℓ => exact congrArg (fun e : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ => e a) (hbaseT ℓ σ)
  ·
    intro τ; exact hF0ι τ
  ·
    intro ℓ τ; exact (hFT ℓ).1 τ
  ·
    intro α σ x
    obtain ⟨ℓ, i⟩ := α
    exact harr ℓ i σ x
  · exact hF00
  · exact hF01
  · intro ℓ; exact ⟨(hFT ℓ).2.1, (hFT ℓ).2.2⟩
  ·
    intro τ hτ; rw [hX1]; exact hpar1 τ hτ
  ·
    intro φ hφ; rw [hX1]; exact hpar2 φ hφ
  ·
    intro τ; rw [hX1]; exact hpar3 τ
  ·
    intro j σ c
    rw [(hgalFC j).1 σ c, ← hdIso₁]; rfl
  ·
    intro j σ c
    rw [(hgalFC j).1 σ c]; rfl
  ·
    intro j c
    rw [(hgalFC j).1 σ₀ c, hsc0]
    show ((Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ 1)).base) c = c
    rw [map_one]; rfl
  ·
    intro j c
    rw [(hgalFC j).1 σ₁ c, hsc1]
    show ((Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ 1)).base) c = c
    rw [map_one]; rfl
  ·
    intro j σ x y hxy
    cases j with
    | none => exact hext0 σ x y hxy
    | some ℓ => exact hextT ℓ σ x y hxy
  ·
    intro j τ y; exact (hgalFC j).2.1 τ y
  ·
    intro j y; exact (hgalFC j).2.2.1 y
  ·
    intro j y; exact (hgalFC j).2.2.2 y
  ·
    intro j σ
    have hd := hdec j σ
    obtain ⟨τ, u, v, hσ, hsc, hn, hχ, hy⟩ := hd
    exact ⟨_, dIso₁ (scalar σ), hn, fun y => hy y⟩
  ·
    intro j σ
    have hd := hdec j σ
    obtain ⟨τ, u, v, hσ, hsc, hn, hχ, hy⟩ := hd
    refine ⟨_, hn, ?_, fun y => hy y⟩
    have e1 : ((MKFunctSign.zmod2Units).comp χS) σ = MKFunctSign.zmod2Units (χS σ) := rfl
    rw [e1, MKFunctSign.zmod2Units_eq_one_iff, hσ,
      CerednikDrinfeld.OmegaSigma.chiS_eq_of_decomposition (ℍ[ℚ, a₂, b₂])ˣ χ₁ ιS σ₀ σ₁ χS hX1 hX2 hX3
        (CerednikDrinfeld.OmegaSigma.normParity q') (w₁ j) (wbar₁ j)
        (CerednikDrinfeld.OmegaSigma.normParity_ne_one_of_nrd_eq q' (w₁ j) (hnw j))
        (CerednikDrinfeld.OmegaSigma.normParity_eq_one_of_nrd_eq q' q (Ne.symm hqq') (wbar₁ j) (hnb j)) τ u v,
      CerednikDrinfeld.OmegaSigma.normParity_eq_one_iff]
  ·
    intro τ h
    show (if χS (ιS τ) = 1 then (1 : ℤˣ) else -1) = 1
    rw [if_pos h]
  ·
    intro τ h
    show (if χS (ιS τ) = 1 then (1 : ℤˣ) else -1) = (if χS σ₀ = 1 then (1 : ℤˣ) else -1)
    rw [if_neg h, if_neg hX2]
  ·
    show (if χS σ₀ = 1 then (1 : ℤˣ) else -1) = -1
    rw [if_neg hX2]
  ·
    show (if χS σ₁ = 1 then (1 : ℤˣ) else -1) = 1
    rw [if_pos hX3]
  ·
    intro α σ φC hφC x
    obtain ⟨ℓ, i⟩ := α
    have hx := (hAL none).2.2.2.2.2 ℓ
    obtain ⟨h6, h8, h7, h9⟩ := hx
    have h0 : (if ((ℓ, i) : HeckeTower.Arr q q').2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ ((ℓ, i) : HeckeTower.Arr q q').1)⁻¹ * w₁ (some ℓ) *
        (if ((ℓ, i) : HeckeTower.Arr q q').2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ ((ℓ, i) : HeckeTower.Arr q q').1) * (w₁ none)⁻¹ ∈ Γ₁ none := by
      by_cases hi : ((ℓ, i) : HeckeTower.Arr q q').2 = 0
      · rw [if_pos hi, inv_one, one_mul, mul_one]; exact h6
      · rw [if_neg hi]; exact h8
    have h1 : (if ((ℓ, i) : HeckeTower.Arr q q').2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ ((ℓ, i) : HeckeTower.Arr q q').1)⁻¹ * wbar₁ (some ℓ) *
        (if ((ℓ, i) : HeckeTower.Arr q q').2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ ((ℓ, i) : HeckeTower.Arr q q').1) * (wbar₁ none)⁻¹ ∈ Γ₁ none := by
      by_cases hi : ((ℓ, i) : HeckeTower.Arr q q').2 = 0
      · rw [if_pos hi, inv_one, one_mul, mul_one]; exact h7
      · rw [if_neg hi]; exact h9
    exact CerednikDrinfeld.OmegaArr.smul_algHom_eq_algHom_smul_of_generators
      A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((Omega.toAmbientOfHom ϖ₁ ρ₁).comp dIso₁) χ₁ ιS σ₀ σ₁ hP
      (Γ₁ none) (Γ₁ (some ℓ)) (w₁ none) (wbar₁ none) (w₁ (some ℓ)) (wbar₁ (some ℓ)) (galFC none) (galFC (some ℓ))
      (hgalFC none).2.1 (hgalFC none).2.2.1 (hgalFC none).2.2.2
      (hgalFC (some ℓ)).2.1 (hgalFC (some ℓ)).2.2.1 (hgalFC (some ℓ)).2.2.2
      _ φC hφC (hw none) (hwbar none) h0 h1 σ x

end S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
end P2MW
export P2MW.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero (solution)
