-- Prove2me | solution 1 for ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5fec1c35-1b27-54c0-96da-de3e3df32223

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level
import Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
import Theorems.Thm_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso
import Theorems.Thm_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
import Theorems.Thm_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq LocalLevel.exists_frobenius_uniformiser_inf_level LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun LocalLevel.exists_fixedLevel_quotientToInvariants_iso LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable LocalLevel.inv_res_inf_eq_index_smul_inv"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw isZero_groupCohomology_one_res_units exists_intermediateField_forall_mem_iff_smul_eq exists_frobenius_uniformiser_inf_level exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun exists_fixedLevel_quotientToInvariants_iso finite_H2_units_and_natCard_le_of_isSolvable inv_res_inf_eq_index_smul_inv"
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

end cohom

end ExtCitation.LocalLevel.Ws25C3

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.isZero_groupCohomology_one_res_units LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq LocalLevel.exists_frobenius_uniformiser_inf_level LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun LocalLevel.exists_fixedLevel_quotientToInvariants_iso LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable LocalLevel.inv_res_inf_eq_index_smul_inv"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw isZero_groupCohomology_one_res_units exists_intermediateField_forall_mem_iff_smul_eq exists_frobenius_uniformiser_inf_level exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun exists_fixedLevel_quotientToInvariants_iso finite_H2_units_and_natCard_le_of_isSolvable inv_res_inf_eq_index_smul_inv"
namespace Ws25C5
p2m_open "ExtCitation.LocalLevel ExtCitation"
open ExtCitation.LocalLevel.Ws25C3

section cohom
variable {G : Type} [Group G] (M : Type) [CommGroup M] [MulDistribMulAction G M]

theorem res_inf_eq_inf_map (N : Subgroup G) [N.Normal] (S : Subgroup G) (c : cocycles₂ (UAN M N)) :
    (groupCohomology.map S.subtype (𝟙 (UAS M S)) 2).hom (((infNatTrans ℤ N 2).app (UA (G := G) M)).hom ((H2π (UAN M N)).hom c)) =
      ((infNatTrans ℤ (N.subgroupOf S) 2).app (UAS M S)).hom
        ((groupCohomology.map (iota N S) (theta M N S) 2).hom ((H2π (UAN M N)).hom c)) := by
  change (groupCohomology.map S.subtype (𝟙 (UAS M S)) 2).hom ((groupCohomology.map (QuotientGroup.mk' N)
      (Rep.ofHom ((UA (G := G) M).ρ.quotientToInvariants_lift N)) 2).hom ((H2π (UAN M N)).hom c)) =
    (groupCohomology.map (QuotientGroup.mk' (N.subgroupOf S)) (Rep.ofHom ((UAS M S).ρ.quotientToInvariants_lift (N.subgroupOf S))) 2).hom
      ((groupCohomology.map (iota N S) (theta M N S) 2).hom ((H2π (UAN M N)).hom c))
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  erw [H2π_comp_map_apply]
  exact congrArg ((H2π (UAS M S)).hom) (Subtype.ext (funext fun p => rfl))

end cohom

theorem forall_mem_zpowers_of_top {G : Type} [Group G] (N : Subgroup G) [N.Normal] (ψ : (⊤ : Subgroup G))
    (hψ : ∀ g : (⊤ : Subgroup G) ⧸ N.subgroupOf ⊤, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf ⊤) ψ)) :
    ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N (ψ : G)) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H g₀ =>
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ (QuotientGroup.mk' (N.subgroupOf ⊤) ⟨g₀, Subgroup.mem_top g₀⟩))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg (iota N ⊤) hk
    rw [map_zpow] at this
    exact this

end ExtCitation.LocalLevel.Ws25C5

open ExtCitation.LocalLevel.Ws25C3 ExtCitation.LocalLevel.Ws25C5 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (NL : Subgroup G) [NL.Normal] (hsolv : Group.IsSolvable (G ⧸ NL))
    (Nn : Subgroup G) [Nn.Normal] (hcard : Nat.card (G ⧸ Nn) = Nat.card (G ⧸ NL))
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) =
      LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) := by
  classical

  obtain ⟨K, instK, hKL, hK⟩ := ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq q L G hG
  haveI : FaithfulSMul (↥NL) L := ⟨fun {s t} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => h x))⟩
  have hGS : ∀ (s : ↥NL) (x : ℚ_[q]), s • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x := fun s x => hG (s : G) x
  have hcompatS : ∀ (s : ↥NL) (u : (↥L)ˣ), ((s • u : (↥L)ˣ) : L) = s • (u : L) := fun s u => hcompat (s : G) u
  obtain ⟨K', instK', hK'L, hK'₀⟩ := ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq q L (↥NL) hGS
  have hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ NL, s • x = x := fun x =>
    (hK'₀ x).trans ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩

  have hKtop : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ s ∈ (⊤ : Subgroup G), s • x = x := fun x =>
    (hK x).trans ⟨fun h s _ => h s, fun h s => h s (Subgroup.mem_top s)⟩
  obtain ⟨ψ₀, -, hψ₀N, hψ₀, -, -, -⟩ := ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level q L G hG hcompat ⊤ K
    (le_of_eq_of_le rfl hKL) hKtop Nn π hπG hπ1 hπmax
  set φ : G := (ψ₀ : G) with hφdef
  have hφN : ∀ g : G ⧸ Nn, g ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ) := forall_mem_zpowers_of_top Nn ψ₀ hψ₀N
  have hfinN : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hφ : ∀ x : L, (∀ n ∈ Nn, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1 :=
    fun x hx hx1 => hψ₀ x (fun n hn => hx n hn.1) hx1

  obtain ⟨inv, hinv⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun q L G hG hcompat
    Nn φ hφN hfinN π hπG hπ1 hπmax
  have hcardNn : Nat.card (groupCohomology (UAN (↥L)ˣ Nn) 2) = Nat.card (G ⧸ NL) := by
    rw [← hcard, ← Nat.card_zmod (Nat.card (G ⧸ Nn))]
    exact Nat.card_congr inv.toEquiv

  obtain ⟨ψ, π', hψN, hψ, hπ'S, hπ'1, hπ'max⟩ := ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level q L G hG hcompat NL K'
    hK'L hK' Nn π hπG hπ1 hπmax
  have hfinψ : IsOfFinOrder (QuotientGroup.mk' (Nn.subgroupOf NL) ψ) := isOfFinOrder_of_finite _
  obtain ⟨inv', hinv'⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun q L (↥NL) hGS hcompatS
    (Nn.subgroupOf NL) ψ hψN hfinψ π' (fun s => hπ'S s.1 s.2) hπ'1 (fun y hy hy1 => hπ'max y (fun n hn => hy ⟨n, hn.2⟩ hn.1) hy1)

  have h90L := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q L G hG hcompat (↥NL) NL.subtype Subtype.val_injective
  have h90n := ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units q L G hG hcompat (↥Nn) Nn.subtype Subtype.val_injective
  obtain ⟨hinjL₀, hrangeL₀⟩ := groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (UA (G := G) (↥L)ˣ) NL h90L
  obtain ⟨hinjn₀, -⟩ := groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (UA (G := G) (↥L)ˣ) Nn h90n
  have hinjL : Function.Injective (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ))) := hinjL₀
  have hinjn : Function.Injective (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (UA (G := G) (↥L)ˣ))) := hinjn₀
  have hrangeL : LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ))) =
      LinearMap.ker (ModuleCat.Hom.hom (groupCohomology.map NL.subtype (𝟙 (UAS (↥L)ˣ NL)) 2)) := hrangeL₀

  have hle : LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (UA (G := G) (↥L)ˣ))) ≤
      LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ))) := by
    rintro _ ⟨β, rfl⟩
    rw [hrangeL]
    suffices h0 : (groupCohomology.map NL.subtype (𝟙 (UAS (↥L)ˣ NL)) 2).hom (((infNatTrans ℤ Nn 2).app (UA (G := G) (↥L)ˣ)).hom β) = 0 by
      exact h0

    obtain ⟨c, rfl⟩ : ∃ c, (H2π (UAN (↥L)ˣ Nn)).hom c = β := (ModuleCat.epi_iff_surjective (H2π (UAN (↥L)ˣ Nn))).mp inferInstance β
    have hxy := res_inf_eq_inf_map (↥L)ˣ Nn NL c
    have hC3 := ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv q L G hG hcompat K hKL hK NL K' hK'L hK' Nn φ hφN hfinN hφ π hπG hπ1
      hπmax ψ hψN hfinψ hψ π' hπ'S hπ'1 hπ'max inv hinv inv' hinv' ((H2π (UAN (↥L)ˣ Nn)).hom c)
      ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c)) hxy

    have hidx : NL.index = Nat.card (G ⧸ Nn) := by rw [hcard, Subgroup.index_eq_card]
    have hzero : NL.index • (((((inv ((H2π (UAN (↥L)ˣ Nn)).hom c)).val : ℚ) / (Nat.card (G ⧸ Nn) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]
      refine ⟨((inv ((H2π (UAN (↥L)ˣ Nn)).hom c)).val : ℤ), ?_⟩
      rw [hidx, nsmul_eq_mul]
      have : (Nat.card (G ⧸ Nn) : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G ⧸ Nn)).ne'
      field_simp
      simp
    rw [hzero, AddCircle.coe_eq_zero_iff] at hC3
    obtain ⟨z, hz⟩ := hC3

    have hm'pos : 0 < Nat.card (↥NL ⧸ Nn.subgroupOf NL) := Nat.card_pos
    haveI : NeZero (Nat.card (↥NL ⧸ Nn.subgroupOf NL)) := ⟨hm'pos.ne'⟩
    have hm'q : (0 : ℚ) < (Nat.card (↥NL ⧸ Nn.subgroupOf NL) : ℚ) := by exact_mod_cast hm'pos
    have hvlt := ZMod.val_lt (inv' ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c)))
    have hz' : (z : ℚ) = ((inv' ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c))).val : ℚ) /
        (Nat.card (↥NL ⧸ Nn.subgroupOf NL) : ℚ) := by
      have h := hz.symm
      rw [zsmul_eq_mul, mul_one] at h
      exact h.symm
    have hz0 : z = 0 := by
      have h1 : (0 : ℚ) ≤ (z : ℚ) := by rw [hz']; positivity
      have h2 : (z : ℚ) < 1 := by
        rw [hz', div_lt_one hm'q]; exact_mod_cast hvlt
      have h1' : (0 : ℤ) ≤ z := by exact_mod_cast h1
      have h2' : z < 1 := by exact_mod_cast h2
      omega
    have hv0 : (inv' ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c))).val = 0 := by
      have : ((inv' ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c))).val : ℚ) /
          (Nat.card (↥NL ⧸ Nn.subgroupOf NL) : ℚ) = 0 := by rw [← hz', hz0]; simp
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · exact_mod_cast h
      · exact absurd h hm'q.ne'
    have hy0 : inv' ((groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c)) = 0 := by
      rw [← ZMod.val_eq_zero, hv0]
    have hy0' : (groupCohomology.map (iota Nn NL) (theta (↥L)ˣ Nn NL) 2).hom ((H2π (UAN (↥L)ˣ Nn)).hom c) = 0 := by
      rw [← map_zero inv'] at hy0
      exact inv'.injective hy0

    exact hxy.trans (by rw [hy0']; exact map_zero _)

  obtain ⟨L', _, _, _, _, hG', hcompat', ⟨e⟩⟩ := ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso q L G hG hcompat NL
  obtain ⟨hfinL', hleL'⟩ := ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable q L' (G ⧸ NL) hsolv hG' hcompat'
  have eH : groupCohomology (UAN (↥L)ˣ NL) 2 ≃ groupCohomology.H2 (Rep.ofMulDistribMulAction (G ⧸ NL) (↥L')ˣ) :=
    ((groupCohomology.functor ℤ (G ⧸ NL) 2).mapIso e).toLinearEquiv.toEquiv
  haveI hfinL : Finite (groupCohomology (UAN (↥L)ˣ NL) 2) :=
    Finite.of_equiv (groupCohomology.H2 (Rep.ofMulDistribMulAction (G ⧸ NL) (↥L')ˣ)) eH.symm
  have hcardL : Nat.card (groupCohomology (UAN (↥L)ˣ NL) 2) ≤ Nat.card (G ⧸ NL) :=
    (Nat.card_congr eH).trans_le hleL'

  have eRn : groupCohomology (UAN (↥L)ˣ Nn) 2 ≃ LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (UA (G := G) (↥L)ˣ))) :=
    (LinearEquiv.ofInjective _ hinjn).toEquiv
  have eRL : groupCohomology (UAN (↥L)ˣ NL) 2 ≃ LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ))) :=
    (LinearEquiv.ofInjective _ hinjL).toEquiv
  have hcardRn : Nat.card (LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (UA (G := G) (↥L)ˣ)))) = Nat.card (G ⧸ NL) := by
    rw [← hcardNn]; exact (Nat.card_congr eRn).symm
  have hcardRL : Nat.card (LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ)))) ≤ Nat.card (G ⧸ NL) := by
    rw [← Nat.card_congr eRL]; exact hcardL
  haveI hfinRL : Finite (LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (UA (G := G) (↥L)ˣ)))) :=
    Finite.of_equiv _ eRL

  symm
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcardRL.trans (le_of_eq hcardRn.symm)

end S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level
end P2MW
export P2MW.S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level (solution)
