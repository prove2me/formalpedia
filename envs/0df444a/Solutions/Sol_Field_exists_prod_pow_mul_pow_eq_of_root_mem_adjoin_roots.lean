-- Prove2me | solution 1 for Field.exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ce38f59c-d823-59bd-bd12-d6601eee5f3a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots

set_option autoImplicit false
set_option maxHeartbeats 800000

open Polynomial IntermediateField

namespace WEK1

theorem add_pred_mul {p : ℕ} (hp : 0 < p) (j : ℕ) : j + (p - 1) * j = p * j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [Nat.succ_sub_one, Nat.succ_mul, add_comm]

theorem step {F E : Type*} [Field F] [Field E] [Algebra F E] {p : ℕ} (hp : p.Prime)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {u : F} (hu : u ≠ 0) {b : E}
    (hb : b ^ p = algebraMap F E u) {z : F} {y : E} (hy : y ^ p = algebraMap F E z)
    (hmem : y ∈ F⟮b⟯) :
    ∃ (j : ℕ) (w : F), z = u ^ j * w ^ p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩

  by_cases hpow : ∃ c : F, c ^ p = u
  · obtain ⟨c, hc⟩ := hpow
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hu (by rw [← hc, zero_pow hp.ne_zero])
    have hb1 : (b / algebraMap F E c) ^ p = 1 := by
      rw [div_pow, hb, ← map_pow, hc, div_self ((_root_.map_ne_zero _).mpr hu)]
    obtain ⟨i, -, hi⟩ :=
      (hζ.map_of_injective (algebraMap F E).injective).eq_pow_of_pow_eq_one hb1
    have hbmem : b ∈ (⊥ : IntermediateField F E) := by
      rw [IntermediateField.mem_bot]
      refine ⟨ζ ^ i * c, ?_⟩
      rw [map_mul, map_pow, hi, div_mul_cancel₀ _ ((_root_.map_ne_zero _).mpr hc0)]
    have hbot : F⟮b⟯ = ⊥ := IntermediateField.adjoin_simple_eq_bot_iff.mpr hbmem
    rw [hbot, IntermediateField.mem_bot] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨0, w, ?_⟩
    rw [pow_zero, one_mul]
    exact (algebraMap F E).injective (by rw [map_pow]; exact hy.symm)

  push Not at hpow
  have H : Irreducible (X ^ p - C u) := X_pow_sub_C_irreducible_of_prime hp hpow
  haveI := Fact.mk H
  have hζ' : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  have hbroot : aeval b (X ^ p - C u) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hb, sub_self]
  let φ : AdjoinRoot (X ^ p - C u) →ₐ[F] E :=
    AdjoinRoot.liftAlgHom (X ^ p - C u) (Algebra.ofId F E) b (by simp [hb])
  have halg : IsAlgebraic F b := ⟨X ^ p - C u, X_pow_sub_C_ne_zero hp.pos u, hbroot⟩
  have hyrange : y ∈ φ.range := by
    have h1 : y ∈ Algebra.adjoin F ({b} : Set E) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
      exact hmem
    refine (Algebra.adjoin_le ?_) h1
    rw [Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root _, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  obtain ⟨y', hy'⟩ := (AlgHom.mem_range φ).mp hyrange
  set α : AdjoinRoot (X ^ p - C u) := AdjoinRoot.root (X ^ p - C u) with hαdef
  have hαp : α ^ p = algebraMap F (AdjoinRoot (X ^ p - C u)) u := by
    rw [AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow p u
  have hy'p : y' ^ p = algebraMap F (AdjoinRoot (X ^ p - C u)) z := by
    apply φ.toRingHom.injective
    show φ (y' ^ p) = φ (algebraMap F _ z)
    rw [map_pow, hy', AlgHom.commutes, hy]

  let ζr : rootsOfUnity p F := hζ.toRootsOfUnity
  have hζr : ((ζr : Fˣ) : F) = ζ := rfl
  let σ : AdjoinRoot (X ^ p - C u) ≃ₐ[F] AdjoinRoot (X ^ p - C u) :=
    autAdjoinRootXPowSubCEquiv hζ' H ζr
  have hσα : σ α = algebraMap F _ ζ * α := by
    show autAdjoinRootXPowSubCEquiv hζ' H ζr (AdjoinRoot.root _) = _
    rw [autAdjoinRootXPowSubCEquiv_root, hζr, Algebra.smul_def]

  by_cases hy0 : y' = 0
  · refine ⟨0, 0, ?_⟩
    rw [hy0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hy'p
    rw [hy'p, zero_pow hp.ne_zero, mul_zero]
  have hz0 : algebraMap F (AdjoinRoot (X ^ p - C u)) z ≠ 0 := by
    rw [← hy'p]; exact pow_ne_zero _ hy0

  have h1 : (σ y' / y') ^ p = 1 := by
    rw [div_pow, ← map_pow, hy'p, AlgEquiv.commutes, div_self hz0]
  obtain ⟨j, -, hj⟩ :=
    (hζ.map_of_injective (algebraMap F (AdjoinRoot (X ^ p - C u))).injective).eq_pow_of_pow_eq_one h1
  have hσy : σ y' = algebraMap F _ ζ ^ j * y' := by
    rw [hj, div_mul_cancel₀ _ hy0]

  have hζp : algebraMap F (AdjoinRoot (X ^ p - C u)) ζ ^ p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have key : algebraMap F (AdjoinRoot (X ^ p - C u)) ζ ^ j *
      algebraMap F (AdjoinRoot (X ^ p - C u)) ζ ^ ((p - 1) * j) = 1 := by
    rw [← pow_add, add_pred_mul hp.pos, pow_mul, hζp, one_pow]
  set w' : AdjoinRoot (X ^ p - C u) := y' * α ^ ((p - 1) * j) with hw'def
  have hσw : σ w' = w' := by
    calc σ w' = (algebraMap F _ ζ ^ j * algebraMap F _ ζ ^ ((p - 1) * j)) *
          (y' * α ^ ((p - 1) * j)) := by
            rw [hw'def, map_mul, map_pow, hσy, hσα, mul_pow]; ring
      _ = w' := by rw [key, one_mul]

  have hζunit : IsPrimitiveRoot (ζr : Fˣ) p := IsPrimitiveRoot.coe_units_iff.mp (by rw [hζr]; exact hζ)
  have hfixpow : ∀ i : ℕ, (σ ^ i) w' = w' := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσw, ih]
  have hfix : ∀ τ : AdjoinRoot (X ^ p - C u) ≃ₐ[F] AdjoinRoot (X ^ p - C u), τ w' = w' := by
    intro τ
    obtain ⟨η, rfl⟩ := (autAdjoinRootXPowSubCEquiv hζ' H).surjective τ
    obtain ⟨i, -, hi⟩ := hζunit.eq_pow_of_mem_rootsOfUnity η.2
    have hη : η = ζr ^ i := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hi.symm)
    rw [hη, map_pow]
    exact hfixpow i

  haveI : IsSplittingField F (AdjoinRoot (X ^ p - C u)) (X ^ p - C u) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hζ' H
  haveI := isGalois_of_isSplittingField_X_pow_sub_C hζ' H (AdjoinRoot (X ^ p - C u))
  haveI : FiniteDimensional F (AdjoinRoot (X ^ p - C u)) :=
    Polynomial.IsSplittingField.finiteDimensional (AdjoinRoot (X ^ p - C u)) (X ^ p - C u)
  have hw'bot : w' ∈ (⊥ : IntermediateField F (AdjoinRoot (X ^ p - C u))) :=
    (IsGalois.mem_bot_iff_fixed w').mpr hfix
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hw'bot

  have hwz : w ^ p = z * u ^ ((p - 1) * j) := by
    apply (algebraMap F (AdjoinRoot (X ^ p - C u))).injective
    rw [map_pow, hw, hw'def, mul_pow, ← pow_mul, hy'p,
      show (p - 1) * j * p = p * ((p - 1) * j) by ring, pow_mul, hαp, ← map_pow, ← map_mul]
  have huj : u ^ j ≠ 0 := pow_ne_zero _ hu
  refine ⟨j, w * (u ^ j)⁻¹, ?_⟩
  symm
  calc u ^ j * (w * (u ^ j)⁻¹) ^ p
      = (u ^ j * u ^ ((p - 1) * j)) * z * ((u ^ j) ^ p)⁻¹ := by rw [mul_pow, inv_pow, hwz]; ring
    _ = z := by
      rw [← pow_add, add_pred_mul hp.pos, pow_mul', mul_comm _ z, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ huj), mul_one]

end WEK1

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) (hp : p.Prime)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (u : Fin n → K) (hu : ∀ i, u i ≠ 0) (β : Fin n → L)
    (hβ : ∀ i, β i ^ p = algebraMap K L (u i))
    (x : K) (hx : x ≠ 0) (γ : L) (hγ : γ ^ p = algebraMap K L x)
    (hmem : γ ∈ IntermediateField.adjoin K (Set.range β)) :
    ∃ (a : Fin n → ℕ) (w : K), x = (∏ i, u i ^ a i) * w ^ p := by
  classical
  induction n generalizing x γ with
  | zero =>
    have h0 : IntermediateField.adjoin K (Set.range β) = ⊥ := by
      rw [Set.range_eq_empty, IntermediateField.adjoin_empty]
    rw [h0, IntermediateField.mem_bot] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨Fin.elim0, w, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact (algebraMap K L).injective (by rw [map_pow]; exact hγ.symm)
  | succ n ih =>
    set b : L := β (Fin.last n) with hbdef
    set un : K := u (Fin.last n) with hundef
    let β' : Fin n → L := β ∘ Fin.castSucc
    let u' : Fin n → K := u ∘ Fin.castSucc
    let K' : IntermediateField K L := IntermediateField.adjoin K (Set.range β')
    have hrange : Set.range β = Set.range β' ∪ {b} := by
      ext t
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff, β', Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨j, rfl⟩ | rfl)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    have hmem' : γ ∈ IntermediateField.adjoin K' ({b} : Set L) := by
      have h := IntermediateField.adjoin_adjoin_left K (Set.range β') ({b} : Set L)
      rw [← hrange] at h
      rw [← IntermediateField.mem_restrictScalars K, h]
      exact hmem
    have hζK' : IsPrimitiveRoot (algebraMap K K' ζ) p :=
      hζ.map_of_injective (algebraMap K K').injective
    have hunK' : algebraMap K K' un ≠ 0 := (_root_.map_ne_zero _).mpr (hu _)
    have hbK' : b ^ p = algebraMap K' L (algebraMap K K' un) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hβ _
    have hγK' : γ ^ p = algebraMap K' L (algebraMap K K' x) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hγ
    obtain ⟨j, w, hjw⟩ := WEK1.step hp hζK' hunK' hbK' hγK' hmem'

    have h1 : algebraMap K L x = algebraMap K L un ^ j * algebraMap K' L w ^ p := by
      have h := congrArg (algebraMap K' L) hjw
      rwa [map_mul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply] at h

    have hx' : x * un ^ ((p - 1) * j) ≠ 0 := mul_ne_zero hx (pow_ne_zero _ (hu _))
    have hγ' : (algebraMap K L un ^ j * algebraMap K' L w) ^ p =
        algebraMap K L (x * un ^ ((p - 1) * j)) := by
      rw [mul_pow, ← pow_mul, map_mul, map_pow, h1, mul_comm j p, ← WEK1.add_pred_mul hp.pos j,
        pow_add]
      ring
    have hmemγ' : algebraMap K L un ^ j * algebraMap K' L w ∈
        IntermediateField.adjoin K (Set.range β') :=
      mul_mem (pow_mem (IntermediateField.algebraMap_mem _ _) _) w.2
    obtain ⟨a', w₀, hx'eq⟩ :=
      ih u' (fun i => hu _) β' (fun i => hβ _) (x * un ^ ((p - 1) * j)) hx' _ hγ' hmemγ'
    have hunj : un ^ j ≠ 0 := pow_ne_zero _ (hu _)
    refine ⟨Fin.snoc a' j, w₀ * (un ^ j)⁻¹, ?_⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    symm
    calc (∏ i : Fin n, u (Fin.castSucc i) ^ a' i) * un ^ j * (w₀ * (un ^ j)⁻¹) ^ p
        = ((∏ i : Fin n, u' i ^ a' i) * w₀ ^ p) * un ^ j * ((un ^ j) ^ p)⁻¹ := by
          rw [mul_pow, inv_pow]
          simp only [u', Function.comp_apply]
          ring
      _ = x * (un ^ j * un ^ ((p - 1) * j)) * ((un ^ j) ^ p)⁻¹ := by rw [← hx'eq]; ring
      _ = x := by
          rw [← pow_add, WEK1.add_pred_mul hp.pos, pow_mul', mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ hunj), mul_one]

end S_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots
end P2MW
export P2MW.S_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots (solution)
