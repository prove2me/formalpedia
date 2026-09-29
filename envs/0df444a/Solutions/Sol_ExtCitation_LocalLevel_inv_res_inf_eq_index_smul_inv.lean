-- Prove2me | solution 1 for ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5256fe1a-48cb-5cd2-91c3-c40bfbdfc1dc

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_exists_carry_H2pi_eq
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
import Theorems.Thm_IntermediateField_exists_uniformiser_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw isZero_groupCohomology_one_res_units exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace Ws25C3
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem exists_norm_eq_zpow (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    (G : Type) [Group G] [MulSemiringAction G L]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ0 : (π : PadicAlgCl q) ≠ 0) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ g : G, g • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖)
    (a : L) (haG : ∀ g : G, g • a = a) (ha0 : (a : PadicAlgCl q) ≠ 0) :
    ∃ k : ℤ, ‖(a : PadicAlgCl q)‖ = ‖(π : PadicAlgCl q)‖ ^ k := by
  obtain ⟨π₀, hπ₀0, hπ₀1, hπ₀⟩ := IntermediateField.exists_uniformiser_padic q K
  have hπK : (π : PadicAlgCl q) ∈ K := (hK π).mpr hπG
  have haK : (a : PadicAlgCl q) ∈ K := (hK a).mpr haG
  obtain ⟨i, hi⟩ := hπ₀ ⟨(π : PadicAlgCl q), hπK⟩ (fun h => hπ0 (by simpa using congrArg Subtype.val h))
  obtain ⟨l, hl⟩ := hπ₀ ⟨(a : PadicAlgCl q), haK⟩ (fun h => ha0 (by simpa using congrArg Subtype.val h))
  simp only at hi hl
  have hπ₀L : (π₀ : PadicAlgCl q) ∈ L := hKL π₀.2
  have hfix : ∀ g : G, g • (⟨(π₀ : PadicAlgCl q), hπ₀L⟩ : L) = ⟨(π₀ : PadicAlgCl q), hπ₀L⟩ :=
    (hK ⟨(π₀ : PadicAlgCl q), hπ₀L⟩).mp π₀.2
  have hle : ‖(π₀ : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖ := hπmax ⟨(π₀ : PadicAlgCl q), hπ₀L⟩ hfix hπ₀1
  set r := ‖(π₀ : PadicAlgCl q)‖ with hr
  have hi1 : i = 1 := by
    have h1 : r ^ i < 1 := by rw [← hi]; exact hπ1
    have h2 : r ≤ r ^ i := by rw [← hi]; exact hle
    have hipos : 0 < i := (zpow_lt_one_iff_right_of_lt_one₀ hπ₀0 hπ₀1).mp h1
    have hnot2 : ¬ (2 ≤ i) := by
      intro h2i
      have h3 : r ^ i ≤ r ^ (2 : ℤ) := zpow_le_zpow_right_of_le_one₀ hπ₀0 hπ₀1.le h2i
      have h4 : r ^ (2 : ℤ) < r := by
        rw [zpow_two]
        exact (mul_lt_mul_of_pos_left hπ₀1 hπ₀0).trans_eq (mul_one r)
      linarith
    omega
  refine ⟨l, ?_⟩
  rw [hl, hi, hi1, zpow_one]

end ExtCitation.LocalLevel.Ws25C3

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw isZero_groupCohomology_one_res_units exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace Ws25C3
p2m_open "ExtCitation.LocalLevel ExtCitation"

section cohom
variable {G : Type} [Group G] (M : Type) [CommGroup M] [MulDistribMulAction G M]

abbrev UA : Rep ℤ G := Rep.ofMulDistribMulAction G M
noncomputable abbrev UAN (N : Subgroup G) [N.Normal] : Rep ℤ (G ⧸ N) := (UA M).quotientToInvariants N
abbrev UAS (S : Subgroup G) : Rep ℤ S := Rep.res S.subtype (UA (G := G) M)
noncomputable abbrev UANS (N : Subgroup G) [N.Normal] (S : Subgroup G) : Rep ℤ (S ⧸ N.subgroupOf S) :=
  (UAS M S).quotientToInvariants (N.subgroupOf S)

abbrev iota (N : Subgroup G) [N.Normal] (S : Subgroup G) : S ⧸ N.subgroupOf S →* G ⧸ N :=
  QuotientGroup.map (N.subgroupOf S) N S.subtype (le_of_eq rfl)

theorem iota_injective (N : Subgroup G) [N.Normal] (S : Subgroup G) : Function.Injective (iota N S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H s =>
    rw [MonoidHom.mem_ker] at hz
    change (QuotientGroup.mk (s : G) : G ⧸ N) = 1 at hz
    rw [QuotientGroup.eq_one_iff] at hz
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hz

theorem mem_invariants_res (N : Subgroup G) [N.Normal] (S : Subgroup G) (v : UAN M N) :
    (v.1 : UA (G := G) M) ∈ Representation.invariants ((UAS M S).ρ.comp (N.subgroupOf S).subtype) := by
  intro n
  exact v.2 ⟨(n : S), n.2⟩

noncomputable def theta (N : Subgroup G) [N.Normal] (S : Subgroup G) : Rep.res (iota N S) (UAN M N) ⟶ UANS M N S :=
  Rep.ofHom
    { toFun := fun v => ⟨v.1, mem_invariants_res M N S v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := by
        intro g
        induction g using QuotientGroup.induction_on with
        | H s => rfl }

theorem theta_apply_val (N : Subgroup G) [N.Normal] (S : Subgroup G) (v : UAN M N) :
    ((theta M N S).hom v).1 = v.1 := rfl

theorem res_inf_carry (N : Subgroup G) [N.Normal] (S : Subgroup G)
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (ψ : S) (hψN : ∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hfinψ : IsOfFinOrder (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (f : ℕ) (hψφ : QuotientGroup.mk' N (ψ : G) = QuotientGroup.mk' N (φ ^ f))
    (a : UAN M N) (ha : (UAN M N).ρ (QuotientGroup.mk' N φ) a = a)
    (hcmem : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ (UAN M N))
    (hct : carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ ((theta M N S).hom a) ∈ cocycles₂ (UANS M N S)) :
    (groupCohomology.map S.subtype (𝟙 (UAS M S)) 2).hom (((infNatTrans ℤ N 2).app (UA (G := G) M)).hom
        ((H2π (UAN M N)).hom ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hcmem⟩)) =
      ((infNatTrans ℤ (N.subgroupOf S) 2).app (UAS M S)).hom
        ((f / Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f) •
          (H2π (UANS M N S)).hom ⟨carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ ((theta M N S).hom a), hct⟩) := by
  have hιψ : iota N S (QuotientGroup.mk' (N.subgroupOf S) ψ) = (QuotientGroup.mk' N φ) ^ f := by
    show (QuotientGroup.mk ((ψ : G)) : G ⧸ N) = (QuotientGroup.mk' N φ) ^ f
    rw [← map_pow]
    exact hψφ
  have hres := groupCohomology.map_carry_H2pi_eq_smul_carry (iota N S) (iota_injective N S) (QuotientGroup.mk' N φ) hφN hfinN f
    (QuotientGroup.mk' (N.subgroupOf S) ψ) hιψ hψN hfinψ (UAN M N) (UANS M N S) (theta M N S) a ha hcmem hct
  rw [← hres]

  change (groupCohomology.map S.subtype (𝟙 (UAS M S)) 2).hom ((groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom ((UA (G := G) M).ρ.quotientToInvariants_lift N)) 2).hom
      ((H2π (UAN M N)).hom ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hcmem⟩)) =
    (groupCohomology.map (QuotientGroup.mk' (N.subgroupOf S)) (Rep.ofHom ((UAS M S).ρ.quotientToInvariants_lift (N.subgroupOf S))) 2).hom
      ((groupCohomology.map (iota N S) (theta M N S) 2).hom ((H2π (UAN M N)).hom ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hcmem⟩))
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  erw [H2π_comp_map_apply]
  exact congrArg ((H2π (UAS M S)).hom) (Subtype.ext (funext fun p => rfl))

end cohom

end ExtCitation.LocalLevel.Ws25C3

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw isZero_groupCohomology_one_res_units exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow"
namespace Ws25C3
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem rho_eq_self_of_generator {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} {a : A} (ha : A.ρ s a = a) (g : G) : A.ρ g a = a := by
  have hpow : ∀ k : ℕ, A.ρ (s ^ k) a = a := by
    intro k
    induction k with
    | zero => rw [pow_zero, MonoidHom.map_one]; rfl
    | succ k ih =>
      rw [pow_succ, MonoidHom.map_mul]
      show A.ρ (s ^ k) (A.ρ s a) = a
      rw [ha, ih]
  obtain ⟨k, hk⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr (hs g)
  simp only at hk
  rw [← hk]
  exact hpow k

theorem coe_val_intCast_div (n : ℕ) (hn : 0 < n) (z : ℤ) :
    (((((z : ZMod n).val : ℚ) / (n : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = ((((z : ℚ) / (n : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hv : (((z : ZMod n).val : ℤ) : ℚ) = ((z % (n : ℤ) : ℤ) : ℚ) := by
    rw [ZMod.val_intCast]
  have hval : (((z : ZMod n).val : ℕ) : ℚ) = (z : ℚ) - (n : ℚ) * ((z / (n : ℤ) : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv z n
    have h2 : (((z : ZMod n).val : ℕ) : ℚ) = (((z : ZMod n).val : ℤ) : ℚ) := by norm_cast
    rw [h2, hv]
    have h3 : ((z % (n : ℤ) : ℤ) : ℚ) + (n : ℚ) * ((z / (n : ℤ) : ℤ) : ℚ) = (z : ℚ) := by exact_mod_cast this
    linarith
  rw [hval]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show ((z : ℚ) - (n : ℚ) * ((z / (n : ℤ) : ℤ) : ℚ)) / (n : ℚ) = (z : ℚ) / n - ((z / (n : ℤ) : ℤ) : ℚ) by field_simp]
  rw [AddCircle.coe_sub]
  conv_rhs => rw [← sub_zero ((((z : ℚ) / (n : ℚ)) : ℚ) : AddCircle (1 : ℚ))]
  congr 1
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨z / (n : ℤ), by simp⟩

end ExtCitation.LocalLevel.Ws25C3

open ExtCitation.LocalLevel.Ws25C3 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (hφ : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (ψ : S) (hψN : ∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hfinψ : IsOfFinOrder (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hψ : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1)
    (π' : (↥L)ˣ) (hπ'S : ∀ s ∈ S, s • π' = π') (hπ'1 : ‖((π' : L) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖)
    (inv : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ≃+ ZMod (Nat.card (G ⧸ N)))
    (hinv : ∀ (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k →
          inv ((H2π ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)).hom
              ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hc⟩) = (k : ZMod (Nat.card (G ⧸ N))))
    (inv' : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) ≃+
        ZMod (Nat.card (S ⧸ N.subgroupOf S)))
    (hinv' : ∀ (a : (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a ∈
          cocycles₂ ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ k →
          inv' ((H2π ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))).hom
              ⟨carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a, hc⟩) = (k : ZMod (Nat.card (S ⧸ N.subgroupOf S))))
    (x : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N))
    (y : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)))
    (hxy : (map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom
        (((infNatTrans ℤ N 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom x) =
      ((infNatTrans ℤ (N.subgroupOf S) 2).app (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))).hom y) :
    (((((inv' y).val : ℚ) / (Nat.card (S ⧸ N.subgroupOf S) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) =
      S.index • (((((inv x).val : ℚ) / (Nat.card (G ⧸ N) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  classical

  obtain ⟨c, rfl⟩ : ∃ c, (H2π (UAN (↥L)ˣ N)).hom c = x :=
    (ModuleCat.epi_iff_surjective (H2π (UAN (↥L)ˣ N))).mp inferInstance x
  obtain ⟨ha, hcmem, hcx⟩ := groupCohomology.exists_carry_H2pi_eq (QuotientGroup.mk' N φ) hφN hfinN c

  have haGN : ∀ g : G ⧸ N, (UAN (↥L)ˣ N).ρ g (cyclicInv (QuotientGroup.mk' N φ) ⇑c) = cyclicInv (QuotientGroup.mk' N φ) ⇑c :=
    rho_eq_self_of_generator (QuotientGroup.mk' N φ) hφN hfinN ha
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : (↥L)ˣ, (cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1 = Additive.ofMul a₀ := ⟨_, rfl⟩
  have htoMul : (Additive.toMul ((cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1 : Additive (↥L)ˣ) : (↥L)ˣ) = a₀ := by
    rw [ha₀]; rfl
  have ha₀G : ∀ g : G, g • a₀ = a₀ := fun g => by
    have h1 : (UA (G := G) (↥L)ˣ).ρ g ((cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1) =
        (cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1 :=
      congrArg Subtype.val (haGN (QuotientGroup.mk g))
    rw [ha₀] at h1
    exact congrArg Additive.toMul h1

  obtain ⟨e, f, he, hf, hef, hππ', hψφ⟩ :=
    ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow q L G hG hcompat K hKL hK S K' hK'L hK' N φ hφ
      π hπG hπ1 hπmax ψ hψ π' hπ'S hπ'1 hπ'max

  have hπ0 : (((π : L) : PadicAlgCl q)) ≠ 0 := fun h => π.ne_zero (by exact_mod_cast h)
  have ha₀0 : (((a₀ : L) : PadicAlgCl q)) ≠ 0 := fun h => a₀.ne_zero (by exact_mod_cast h)
  have hπGL : ∀ g : G, g • (π : L) = (π : L) := fun g => by rw [← hcompat, hπG]
  have ha₀GL : ∀ g : G, g • (a₀ : L) = (a₀ : L) := fun g => by rw [← hcompat, ha₀G]
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow q L G K hKL hK (π : L) hπGL hπ0 hπ1
    (fun y hy hy1 => hπmax y (fun n _ => hy n) hy1) _ ha₀GL ha₀0
  have hk' : ‖(((a₀ : L) : PadicAlgCl q))‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ ((e : ℤ) * k) := by
    rw [hk, hππ', zpow_mul, zpow_natCast]

  have hinvx : inv ((H2π (UAN (↥L)ˣ N)).hom c) = (k : ZMod (Nat.card (G ⧸ N))) := by
    rw [← hcx]
    exact hinv _ k hcmem (by rw [htoMul]; exact hk)

  have hct : carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ ((theta (↥L)ˣ N S).hom (cyclicInv (QuotientGroup.mk' N φ) ⇑c)) ∈
      cocycles₂ (UANS (↥L)ˣ N S) := by
    refine groupCohomology.carryFun_mem_cocycles2 _ _ _ _ ?_
    apply Subtype.ext
    change (UA (G := G) (↥L)ˣ).ρ ((ψ : S) : G) ((cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1) =
      (cyclicInv (QuotientGroup.mk' N φ) ⇑c : UAN (↥L)ˣ N).1
    exact congrArg Subtype.val (haGN (QuotientGroup.mk ((ψ : S) : G)))

  have hcore := res_inf_carry (↥L)ˣ N S φ hφN hfinN ψ hψN hfinψ f hψφ _ ha hcmem hct

  have hinj : Function.Injective ((infNatTrans ℤ (N.subgroupOf S) 2).app (UAS (↥L)ˣ S)).hom := by
    have h90 := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q L G hG hcompat (↥(N.subgroupOf S))
      (S.subtype.comp (N.subgroupOf S).subtype) (Subtype.val_injective.comp Subtype.val_injective)
    exact (groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (UAS (↥L)ˣ S) (N.subgroupOf S) h90).1
  have hy : y = (f / Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f) •
      (H2π (UANS (↥L)ˣ N S)).hom ⟨carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ ((theta (↥L)ˣ N S).hom _), hct⟩ := by
    apply hinj
    rw [← hxy, ← hcx, hcore]

  have hordφ : orderOf (QuotientGroup.mk' N φ) = Nat.card (G ⧸ N) := by
    rw [← Nat.card_zpowers, (Subgroup.eq_top_iff' _).mpr hφN, Subgroup.card_top]
  have hordψ : orderOf (QuotientGroup.mk' (N.subgroupOf S) ψ) = Nat.card (S ⧸ N.subgroupOf S) := by
    rw [← Nat.card_zpowers, (Subgroup.eq_top_iff' _).mpr hψN, Subgroup.card_top]
  have hιψ : iota N S (QuotientGroup.mk' (N.subgroupOf S) ψ) = (QuotientGroup.mk' N φ) ^ f := by
    show (QuotientGroup.mk ((ψ : G)) : G ⧸ N) = (QuotientGroup.mk' N φ) ^ f
    rw [← map_pow]; exact hψφ
  have hgm : Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f ∣ Nat.card (G ⧸ N) := by
    rw [hordφ]; exact Nat.gcd_dvd_left _ f
  have hgf : Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f ∣ f := Nat.gcd_dvd_right _ f
  have hmpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have hm'pos : 0 < Nat.card (S ⧸ N.subgroupOf S) := Nat.card_pos
  have hgpos : 0 < Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f := Nat.pos_of_dvd_of_pos hgm hmpos
  obtain ⟨m'', hm''⟩ := hgm
  obtain ⟨f', hf'⟩ := hgf
  have hfg : f / Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f = f' := Nat.div_eq_of_eq_mul_left hgpos (by rw [mul_comm]; exact hf')
  have hm'eq : Nat.card (S ⧸ N.subgroupOf S) = m'' := by
    rw [← hordψ, ← orderOf_injective (iota N S) (iota_injective N S), hιψ, orderOf_pow' _ hf.ne']
    have h := hm''
    rw [← hordφ] at h
    exact Nat.div_eq_of_eq_mul_left hgpos (by rw [mul_comm]; exact h)

  have hinv'y : inv' y = (((f' * e : ℕ) : ℤ) * k : ℤ) := by
    rw [hy, map_nsmul, hinv' _ ((e : ℤ) * k) hct (by rw [show (Additive.toMul (((theta (↥L)ˣ N S).hom
        (cyclicInv (QuotientGroup.mk' N φ) ⇑c) : UANS (↥L)ˣ N S).1 : Additive (↥L)ˣ) : (↥L)ˣ) = a₀ from htoMul]; exact hk'),
      nsmul_eq_mul, hfg]
    push_cast
    ring

  rw [hinv'y, hinvx, coe_val_intCast_div _ hm'pos, coe_val_intCast_div _ hmpos, ← hef]
  rw [← AddCircle.coe_nsmul]
  congr 1
  have hm'q : (Nat.card (S ⧸ N.subgroupOf S) : ℚ) ≠ 0 := by exact_mod_cast hm'pos.ne'
  have hmq : (Nat.card (G ⧸ N) : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hgq : (Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hmrel : (Nat.card (G ⧸ N) : ℚ) = (Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f : ℚ) * (Nat.card (S ⧸ N.subgroupOf S) : ℚ) := by
    rw [hm'eq]; exact_mod_cast hm''
  have hfrel : (f : ℚ) = (Nat.gcd (orderOf (QuotientGroup.mk' N φ)) f : ℚ) * (f' : ℚ) := by exact_mod_cast hf'
  rw [nsmul_eq_mul]
  push_cast
  rw [hmrel, hfrel]
  field_simp

end S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv
end P2MW
export P2MW.S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv (solution)
