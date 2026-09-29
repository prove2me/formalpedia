-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_padicValRat_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/abf093c4-ebed-5b68-92a6-3853fbfaf2bf

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_padicValRat_nrd
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

open scoped MatrixGroups Quaternion

noncomputable section

namespace TypePreservingNrdCC

section Quadratic

variable {R : Type*} [CommRing R] {a b : R}

theorem sq_sub_trd_smul_add_nrd (x : ℍ[R, a, b]) :
    x * x - QuaternionAlgebra.trd x • x + QuaternionAlgebra.nrd x • (1 : ℍ[R, a, b]) = 0 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

theorem nrd_add_add_nrd_sub (x y : ℍ[R, a, b]) :
    QuaternionAlgebra.nrd (x + y) + QuaternionAlgebra.nrd (x - y) =
      2 * QuaternionAlgebra.nrd x + 2 * QuaternionAlgebra.nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp [QuaternionAlgebra.nrd]
  ring

theorem i_mul_j_ne_j_mul_i (h2 : (2 : R) ≠ 0) :
    (⟨0, 1, 0, 0⟩ : ℍ[R, a, b]) * ⟨0, 0, 1, 0⟩ ≠ (⟨0, 0, 1, 0⟩ : ℍ[R, a, b]) * ⟨0, 1, 0, 0⟩ := by
  intro h
  have hk := congrArg QuaternionAlgebra.imK h
  simp at hk

  apply h2
  linear_combination hk

end Quadratic

section Matrices

variable {K : Type*} [Field K]

theorem mat_sq_sub_trace_smul_add_det (A : Matrix (Fin 2) (Fin 2) K) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem det_eq_or_exists_eq_smul_one (A : Matrix (Fin 2) (Fin 2) K) (t n : K)
    (h : A * A - t • A + n • (1 : Matrix (Fin 2) (Fin 2) K) = 0) :
    A.det = n ∨ ∃ κ : K, A = κ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 := mat_sq_sub_trace_smul_add_det A
  have h3 : (A.trace - t) • A = (A.det - n) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := sub_eq_zero.2 (h.trans h2.symm)
    rw [sub_smul, sub_smul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    convert this using 1
    abel
  by_cases ht : A.trace = t
  · left
    rw [ht, sub_self, zero_smul] at h3
    have := congrFun (congrFun h3.symm 0) 0
    simp at this
    exact sub_eq_zero.1 this
  · right
    have hne : A.trace - t ≠ 0 := sub_ne_zero.2 ht
    have := congrArg (fun M => (A.trace - t)⁻¹ • M) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    exact ⟨_, this⟩

theorem det_add_add_det_sub (X Y : Matrix (Fin 2) (Fin 2) K) :
    (X + Y).det + (X - Y).det = 2 * X.det + 2 * Y.det := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply]
  ring

end Matrices

section Chart

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] {a b : F}

theorem det_algHom_eq_nrd (h2 : (2 : K) ≠ 0)
    (ι : ℍ[F, a, b] →ₐ[F] Matrix (Fin 2) (Fin 2) K) (hι : Function.Injective ι) (x : ℍ[F, a, b]) :
    (ι x).det = algebraMap F K (QuaternionAlgebra.nrd x) := by

  let S : ℍ[F, a, b] → Prop := fun y => ∃ c : K, ι y = c • (1 : Matrix (Fin 2) (Fin 2) K)

  have key : ∀ y : ℍ[F, a, b], ¬ S y → (ι y).det = algebraMap F K (QuaternionAlgebra.nrd y) := by
    intro y hy
    have hrel : ι y * ι y - algebraMap F K (QuaternionAlgebra.trd y) • ι y +
        algebraMap F K (QuaternionAlgebra.nrd y) • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
      have h0 := congrArg ι (sq_sub_trd_smul_add_nrd y)
      rw [map_add, map_sub, map_mul, map_smul, map_smul, map_one, map_zero] at h0
      rwa [algebraMap_smul, algebraMap_smul]
    rcases det_eq_or_exists_eq_smul_one _ _ _ hrel with h | h
    · exact h
    · exact absurd h hy

  have h2F : (2 : F) ≠ 0 := by
    intro h
    apply h2
    have := congrArg (algebraMap F K) h
    rwa [map_ofNat, map_zero] at this

  have hex : ∃ y : ℍ[F, a, b], ¬ S y := by
    by_contra hall
    push Not at hall
    obtain ⟨ci, hi⟩ := hall ⟨0, 1, 0, 0⟩
    obtain ⟨cj, hj⟩ := hall ⟨0, 0, 1, 0⟩
    apply i_mul_j_ne_j_mul_i (a := a) (b := b) h2F
    apply hι
    rw [map_mul, map_mul, hi, hj, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ci cj]

  have hS : ∀ y z : ℍ[F, a, b], S y → S z → S (y - z) := by
    rintro y z ⟨cy, hy⟩ ⟨cz, hz⟩
    exact ⟨cy - cz, by rw [map_sub, hy, hz, sub_smul]⟩
  by_cases hx : S x
  · obtain ⟨y, hy⟩ := hex
    have h1 : ¬ S (x + y) := fun h => hy (by simpa using hS _ _ h hx)
    have h1' : ¬ S (x - y) := fun h => hy (by simpa using hS _ _ hx h)
    have e1 := key _ h1
    have e2 := key _ h1'
    have e3 := key _ hy
    have pm := det_add_add_det_sub (ι x) (ι y)
    rw [← map_add, ← map_sub, e1, e2, e3, ← map_add, nrd_add_add_nrd_sub, map_add, map_mul, map_mul,
      map_ofNat] at pm
    have pm' := add_right_cancel pm
    exact (mul_left_cancel₀ h2 pm').symm
  · exact key x hx

end Chart

section Local

variable {R₀ : Type*} [CommRing R₀] [IsLocalRing R₀] {K₀ : Type*} [Field K₀] [CharZero K₀]
  [Algebra R₀ K₀]

theorem isUnit_intCast_of_not_dvd (r : ℕ) [hr : Fact r.Prime] (hru : ¬ IsUnit ((r : ℕ) : R₀))
    {n : ℤ} (hn : ¬ (r : ℤ) ∣ n) : IsUnit ((n : ℤ) : R₀) := by
  by_contra hu
  have hp : Prime (r : ℤ) := Nat.prime_iff_prime_int.1 hr.out
  obtain ⟨α, β, hαβ⟩ := (Prime.coprime_iff_not_dvd hp).2 hn
  have hcast := congrArg (Int.cast : ℤ → R₀) hαβ
  push_cast at hcast
  have hmem : (α : R₀) * (r : R₀) + (β : R₀) * (n : R₀) ∈ nonunits R₀ :=
    IsLocalRing.nonunits_add (mul_mem_nonunits_right hru) (mul_mem_nonunits_right hu)
  rw [hcast] at hmem
  exact hmem isUnit_one

theorem isUnit_natCast_of_not_dvd (r : ℕ) [hr : Fact r.Prime] (hru : ¬ IsUnit ((r : ℕ) : R₀))
    {n : ℕ} (hn : ¬ r ∣ n) : IsUnit ((n : ℕ) : R₀) := by
  have h := isUnit_intCast_of_not_dvd (R₀ := R₀) r hru (n := (n : ℤ)) (by exact_mod_cast hn)
  rwa [Int.cast_natCast] at h

theorem exists_units_natCast_eq_mul_pow (r : ℕ) [hr : Fact r.Prime] (hru : ¬ IsUnit ((r : ℕ) : R₀))
    {n : ℕ} (hn : n ≠ 0) :
    ∃ u : R₀ˣ, (n : K₀) = algebraMap R₀ K₀ u * (r : K₀) ^ padicValNat r n := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn r hr.out.one_lt.ne'
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd (R₀ := R₀) r hru hn'
  have hn'0 : n' ≠ 0 := fun h => hn' (h ▸ dvd_zero r)
  refine ⟨u, ?_⟩
  rw [padicValNat.mul (pow_ne_zero _ hr.out.ne_zero) hn'0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hn', add_zero, hu, map_natCast]
  push_cast
  ring

theorem exists_units_ratCast_eq_mul_zpow (r : ℕ) [hr : Fact r.Prime] (hru : ¬ IsUnit ((r : ℕ) : R₀))
    {q : ℚ} (hq : q ≠ 0) :
    ∃ u : R₀ˣ, (q : K₀) = algebraMap R₀ K₀ u * (r : K₀) ^ padicValRat r q := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.2 hq
  have habs : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hnum
  have hden : q.den ≠ 0 := q.den_nz
  obtain ⟨u₁, h₁⟩ := exists_units_natCast_eq_mul_pow (R₀ := R₀) (K₀ := K₀) r hru habs
  obtain ⟨u₂, h₂⟩ := exists_units_natCast_eq_mul_pow (R₀ := R₀) (K₀ := K₀) r hru hden

  have hsgn : IsUnit q.num.sign := Int.isUnit_iff_natAbs_eq.2 (Int.natAbs_sign_of_ne_zero hnum)
  obtain ⟨s, hs⟩ := hsgn.map (Int.castRingHom R₀)
  have hr0 : (r : K₀) ≠ 0 := by exact_mod_cast hr.out.ne_zero
  have hu₂ : (algebraMap R₀ K₀ u₂ : K₀) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero.2 hden : (q.den : K₀) ≠ 0)
    rw [h₂, h, zero_mul]
  refine ⟨s * u₁ * u₂⁻¹, ?_⟩
  have hq' : (q : K₀) = ((q.num.sign : ℤ) : K₀) * (q.num.natAbs : K₀) / (q.den : K₀) := by
    rw [Rat.cast_def]
    congr 1
    conv_lhs => rw [← Int.sign_mul_natAbs q.num]
    rw [Int.cast_mul, Int.cast_natCast]
  have hval : padicValRat r q = (padicValNat r q.num.natAbs : ℤ) - (padicValNat r q.den : ℤ) := by
    rw [padicValRat_def, padicValInt]
  have hsK : ((q.num.sign : ℤ) : K₀) = algebraMap R₀ K₀ s := by
    rw [hs, Int.coe_castRingHom, map_intCast]
  rw [hq', hval, zpow_sub₀ hr0, zpow_natCast, zpow_natCast, h₁, h₂, hsK, Units.val_mul, Units.val_mul,
    map_mul, map_mul, map_units_inv]
  field_simp

end Local

section Uniformiser

open ValuationSubring

theorem irreducible_natCast
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1) :
    Irreducible ((r : ℕ) : R₀) := by
  obtain ⟨hmem, -, hrest⟩ :=
    ValuationSubring.isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
      r A hA
  set O₀ := (Valued.v.comap (ratClosure A).subtype).valuationSubring with hO₀
  have hirr := (hrest hmem).1
  have hrange : ∀ y : ↥(ratClosure A), y ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔ y ∈ O₀ := by
    intro y
    rw [hR₀ y, hO₀, Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
    rfl
  let f : R₀ →+* ↥O₀ := (algebraMap R₀ ↥(ratClosure A)).codRestrict O₀ fun x => (hrange _).1 ⟨x, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => IsFractionRing.injective R₀ ↥(ratClosure A) (congrArg Subtype.val h), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := (hrange (y : ↥(ratClosure A))).2 y.2
    exact ⟨x, Subtype.ext hx⟩
  let e : R₀ ≃+* ↥O₀ := RingEquiv.ofBijective f hf
  have he : e ((r : ℕ) : R₀) =
      ⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), hmem⟩ := by
    apply Subtype.ext
    show algebraMap R₀ ↥(ratClosure A) r = _
    rw [map_natCast]
    apply Subtype.ext
    simp
  have h' : Irreducible (e ((r : ℕ) : R₀)) := by
    rw [he]
    exact hirr
  exact (MulEquiv.irreducible_iff e).1 h'

end Uniformiser

end TypePreservingNrdCC

end

open scoped MatrixGroups Quaternion
open CerednikDrinfeld LT.LatticeTree QuaternionAlgebra ValuationSubring

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x))
    [MulAction (ℍ[ℚ, a, b])ˣ (LT.LatticeTree.Vertex R₀ ↥(ratClosure A))]
    (hact : ∀ (g : (ℍ[ℚ, a, b])ˣ) (x : LT.LatticeTree.Vertex R₀ ↥(ratClosure A)), g • x = ρ g • x)
    (x : (ℍ[ℚ, a, b])ˣ) :
    x ∈ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
        (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A)) ↔
      Even (padicValRat r (nrd (x : ℍ[ℚ, a, b]))) := by

  have hirr : Irreducible ((r : ℕ) : R₀) := TypePreservingNrdCC.irreducible_natCast r A hA R₀ hR₀

  set m : GL (Fin 2) ↥(ratClosure A) :=
    Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x with hm
  have h2 : (2 : ↥(ratClosure A)) ≠ 0 := two_ne_zero
  have hdet : Matrix.det (m : Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) =
      algebraMap ℚ ↥(ratClosure A) (nrd (x : ℍ[ℚ, a, b])) := by
    rw [hm, Units.coe_map, MonoidHom.coe_coe]
    exact TypePreservingNrdCC.det_algHom_eq_nrd h2 ι hι (x : ℍ[ℚ, a, b])

  have hn0 : nrd (x : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h0
    have hu : IsUnit (Matrix.det (m : Matrix (Fin 2) (Fin 2) ↥(ratClosure A))) :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m)
    rw [hdet, h0, map_zero] at hu
    exact not_isUnit_zero hu

  obtain ⟨u, hu⟩ := TypePreservingNrdCC.exists_units_ratCast_eq_mul_zpow (R₀ := R₀)
    (K₀ := ↥(ratClosure A)) r hirr.not_isUnit hn0
  have hdet' : Matrix.det (m : Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) =
      algebraMap R₀ ↥(ratClosure A) u *
        algebraMap R₀ ↥(ratClosure A) ((r : ℕ) : R₀) ^ padicValRat r (nrd (x : ℍ[ℚ, a, b])) := by
    rw [hdet, eq_ratCast, hu, map_natCast]
  exact CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_of_det_eq_mul_zpow R₀ ↥(ratClosure A)
    ((r : ℕ) : R₀) hirr (ℍ[ℚ, a, b])ˣ ρ hact x m (hρ x) u (padicValRat r (nrd (x : ℍ[ℚ, a, b]))) hdet'

end S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_padicValRat_nrd
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_padicValRat_nrd (solution)
