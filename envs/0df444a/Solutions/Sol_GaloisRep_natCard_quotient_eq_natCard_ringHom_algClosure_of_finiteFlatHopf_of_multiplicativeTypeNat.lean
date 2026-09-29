-- Prove2me | solution 1 for GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5413e49d-d1a8-5418-b9fa-611c4e835a6e

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_GaloisRep_exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf
import Theorems.Thm_GaloisRep_finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

namespace F2DEngine

private lemma exists_mem_inertia_not_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (hm : m ≠ 0)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) :
    ∃ σ ∈ Aq.inertiaSubgroupIn ℚ, ¬ ((q : ℤ) ∣ (n σ : ℤ) - 1) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨σ, hσI, hσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow Aq hq hAq (-1)
  refine ⟨σ, hσI, fun hdvd => ?_⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) q
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  have hζqm : ζ ^ q ^ m = 1 := by
    obtain ⟨c, hc⟩ := dvd_pow_self q hm
    rw [hc, pow_mul, hζq, one_pow]
  have h1 : ζ ^ n σ = ζ ^ ((-1 : (ZMod q)ˣ) : ZMod q).val :=
    (hn σ ζ hζqm).symm.trans (hσ ζ hζq)
  have hord : orderOf ζ = q := (hζ.eq_orderOf).symm
  have h2 : (n σ : ZMod q) = (((-1 : (ZMod q)ˣ) : ZMod q).val : ZMod q) := by
    rw [ZMod.natCast_eq_natCast_iff]
    have h1' : ζ ^ (n σ % orderOf ζ) = ζ ^ (((-1 : (ZMod q)ˣ) : ZMod q).val % orderOf ζ) := by
      rw [pow_mod_orderOf, pow_mod_orderOf]
      exact h1
    rw [hord] at h1'
    exact hζ.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1'
  have h3 : (n σ : ZMod q) = 1 := by
    have h0 : (((n σ : ℤ) - 1 : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
    push_cast at h0
    exact sub_eq_zero.mp h0
  have h5 : ((-1 : (ZMod q)ˣ) : ZMod q) = 1 := by
    have hval : ((((-1 : (ZMod q)ˣ) : ZMod q)).val : ZMod q) = ((-1 : (ZMod q)ˣ) : ZMod q) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [← hval, ← h2]
    exact h3
  have h6 : ((-1 : (ZMod q)ˣ) : ZMod q) = -1 := by
    rw [Units.val_neg, Units.val_one]
  rw [h6] at h5
  haveI : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  exact ZMod.neg_one_ne_one h5

private lemma mem_of_zsmul_mem_of_coprime {J : Type} [AddCommGroup J] (K : AddSubgroup J)
    {x : J} {c t : ℤ} (hcop : IsCoprime c t) (hc : c • x ∈ K) (ht : t • x = 0) : x ∈ K := by
  obtain ⟨u, v, huv⟩ := hcop
  have hx : x = u • (c • x) + v • (t • x) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, huv, one_smul]
  rw [hx, ht, smul_zero, add_zero]
  exact K.zsmul_mem hc u

end F2DEngine

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
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
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (htors : ∀ x : ↥M, q ^ m • x = 0)
    (W : AddSubgroup J) (hWM : W ≤ M)
    (hμ : ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W)
    (hcos : ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ W) :
    Nat.card (↥M ⧸ W.addSubgroupOf M) = Nat.card (H →+* AlgebraicClosure (ZMod q)) := by
  have _ := hWM
  obtain ⟨K, -, hKchar, hKabs, hKcount⟩ :=
    GaloisRep.exists_addSubgroup_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf
      q H M e he_add he_act Aq hAq
  have hch3 := GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
    q hq2 H M e he_add he_act Aq hAq W hcos
  have hWK : W.addSubgroupOf M = K.addSubgroupOf M := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hM0 : ∀ x : ↥M, x = 0 := fun x => by
        have hx := htors x
        rwa [hm0, pow_zero, one_nsmul] at hx
      ext x
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf, hM0 x]
      simp
    · obtain ⟨σ, hσI, hσn⟩ := F2DEngine.exists_mem_inertia_not_dvd q hq2 Aq hAq m hmpos.ne' n hn
      have hq : q.Prime := Fact.out
      have hcop : IsCoprime ((n σ : ℤ) - 1) ((q : ℤ) ^ m) :=
        (((Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hσn).symm).pow_right
      ext x
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]
      have h2 : ((q : ℤ) ^ m) • (x : J) = 0 := by
        have hc : ((q ^ m • x : ↥M) : J) = q ^ m • (x : J) :=
          AddMonoidHom.map_nsmul M.subtype (q ^ m) x
        have h0 : ((q ^ m : ℕ) : ℤ) • (x : J) = 0 := by
          rw [natCast_zsmul, ← hc, htors x, ZeroMemClass.coe_zero]
        rwa [Nat.cast_pow] at h0
      constructor
      · intro hxW
        have hμx : σ • (x : J) = n σ • (x : J) := hμ σ hσI (x : J) hxW
        have h1 : ((n σ : ℤ) - 1) • (x : J) ∈ K := by
          have heq : ((n σ : ℤ) - 1) • (x : J) = σ • (x : J) - (x : J) := by
            rw [sub_zsmul, natCast_zsmul, one_zsmul, hμx, sub_eq_add_neg]
          rw [heq]
          exact hKabs σ hσI (x : J) x.2
        exact F2DEngine.mem_of_zsmul_mem_of_coprime K hcop h1 h2
      · intro hxK
        have hmem : ((e (e.symm x) : ↥M) : J) ∈ K := by
          rw [Equiv.apply_symm_apply]
          exact hxK
        have hW := hch3 (e.symm x) ((hKchar (e.symm x)).mp hmem)
        rwa [Equiv.apply_symm_apply] at hW
  rw [hWK]
  exact hKcount

end S_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
end P2MW
export P2MW.S_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat (solution)
