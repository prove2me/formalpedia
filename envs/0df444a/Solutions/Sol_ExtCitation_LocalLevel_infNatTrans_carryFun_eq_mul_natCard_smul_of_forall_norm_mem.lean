-- Prove2me | solution 1 for ExtCitation.LocalLevel.infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7b7a27f8-c1f9-5d00-bf27-99882c631ba3

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass Rw exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass finite_H2_units_and_natCard_le_of_isSolvable existsUnique_isLocalFundamentalClass map_eq_natCard_smul_of_isLocalFundamentalClass exists_valuation_units_Kw"
namespace Prop6
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem carryFun_add {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (x y : A) :
    carryFun s hs hfin (x + y) = carryFun s hs hfin x + carryFun s hs hfin y := by
  funext p
  simp only [carryFun, Pi.add_apply]
  split_ifs <;> simp

theorem carryFun_zero {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} : carryFun s hs hfin (0 : A) = 0 := by
  funext p
  simp only [carryFun, Pi.zero_apply]
  split_ifs <;> simp

section Main

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)

noncomputable abbrev incl : (↥K)ˣ →* (↥M)ˣ := Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom

include hcompat in

theorem smul_incl (h : H) (a : (↥K)ˣ) : h • incl q M H K hK a = incl q M H K hK a := by
  apply Units.ext
  rw [hcompat]
  have hmem : (((incl q M H K hK a : (↥M)ˣ) : M) : PadicAlgCl q) ∈ K := by
    change ((IntermediateField.inclusion hK.le (a : K) : M) : PadicAlgCl q) ∈ K
    simp
  exact (hK.mem_iff _).1 hmem h

include hcompat in
theorem ofMul_incl_mem (H' : Subgroup H) (a : (↥K)ˣ) :
    (Additive.ofMul (incl q M H K hK a) : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp H'.subtype) :=
  fun h => congrArg Additive.ofMul (smul_incl q M H hcompat K hK (h : H) a)

noncomputable def inclInv (H' : Subgroup H) [H'.Normal] (a : (↥K)ˣ) :
    (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H' :=
  ⟨Additive.ofMul (incl q M H K hK a), ofMul_incl_mem q M H hcompat K hK H' a⟩

include hcompat in
theorem inclInv_mul (H' : Subgroup H) [H'.Normal] (a b : (↥K)ˣ) :
    inclInv q M H hcompat K hK H' (a * b) = inclInv q M H hcompat K hK H' a + inclInv q M H hcompat K hK H' b := by
  apply Subtype.ext
  simp only [inclInv, map_mul]
  rfl

end Main

section Chi
variable {G : Type} [Group G] {N : ℕ}

def chiVal (χ : G →* Multiplicative (ZMod N)) (g : G) : ℕ := (Multiplicative.toAdd (χ g) : ZMod N).val

def chiCarry (χ : G →* Multiplicative (ZMod N)) (g h : G) : ℕ := (chiVal χ g + chiVal χ h) / N

def chiCorr (χ χ' : G →* Multiplicative (ZMod N)) (g : G) : ℕ := (chiVal χ g + chiVal χ' g) / N

def chiCocycle (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A) : G × G → A :=
  fun p => if N ≤ chiVal χ p.1 + chiVal χ p.2 then a else 0

variable [NeZero N]

theorem chiVal_lt (χ : G →* Multiplicative (ZMod N)) (g : G) : chiVal χ g < N := ZMod.val_lt _

theorem chiVal_one (χ : G →* Multiplicative (ZMod N)) : chiVal χ 1 = 0 := by
  simp [chiVal]

theorem chiVal_one_hom (g : G) : chiVal (1 : G →* Multiplicative (ZMod N)) g = 0 := by
  simp [chiVal]

theorem chiVal_mul (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiVal χ (g * h) = (chiVal χ g + chiVal χ h) % N := by
  simp only [chiVal, map_mul, toAdd_mul, ZMod.val_add]

theorem chiVal_add_chiVal (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiVal χ g + chiVal χ h = chiVal χ (g * h) + N * chiCarry χ g h := by
  rw [chiVal_mul, chiCarry]; exact (Nat.mod_add_div _ _).symm

theorem chiVal_mul_hom (χ χ' : G →* Multiplicative (ZMod N)) (g : G) :
    chiVal χ g + chiVal χ' g = chiVal (χ * χ') g + N * chiCorr χ χ' g := by
  simp only [chiVal, chiCorr, MonoidHom.mul_apply, toAdd_mul, ZMod.val_add]
  exact (Nat.mod_add_div _ _).symm

theorem chiCarry_eq_ite (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiCarry χ g h = if N ≤ chiVal χ g + chiVal χ h then 1 else 0 := by
  have h1 := chiVal_lt χ g
  have h2 := chiVal_lt χ h
  have hN : 0 < N := Nat.pos_of_neZero N
  unfold chiCarry
  split_ifs with hle
  · apply Nat.div_eq_of_lt_le <;> omega
  · exact Nat.div_eq_of_lt (by omega)

theorem chiCocycle_apply (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A) (g h : G) :
    chiCocycle χ a (g, h) = (chiCarry χ g h : ℤ) • a := by
  simp only [chiCocycle, chiCarry_eq_ite]
  split_ifs <;> simp

theorem chiCocycle_one {A : Rep ℤ G} (a : A) : chiCocycle (1 : G →* Multiplicative (ZMod N)) a = 0 := by
  funext p
  have hN : 0 < N := Nat.pos_of_neZero N
  simp only [chiCocycle, chiVal_one_hom, add_zero, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem chiCocycle_mem_cocycles₂ (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) : chiCocycle χ a ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff]
  intro g h j
  simp only [chiCocycle_apply, map_zsmul, ha, ← add_smul]
  congr 1
  have h1 := chiVal_add_chiVal χ g h
  have h2 := chiVal_add_chiVal χ (g * h) j
  have h3 := chiVal_add_chiVal χ h j
  have h4 := chiVal_add_chiVal χ g (h * j)
  rw [mul_assoc] at h2
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have key : (N : ℤ) * ((chiCarry χ (g * h) j : ℤ) + chiCarry χ g h) =
      (N : ℤ) * ((chiCarry χ h j : ℤ) + chiCarry χ g (h * j)) := by
    push_cast [Nat.cast_add, Nat.cast_mul] at h1 h2 h3 h4 ⊢
    zify at h1 h2 h3 h4
    linear_combination h3 + h4 - h1 - h2
  exact mul_left_cancel₀ hN key

theorem chiCocycle_mul_eq (χ χ' : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) :
    chiCocycle (χ * χ') a = chiCocycle χ a + chiCocycle χ' a -
      (d₁₂ A).hom (fun g => (chiCorr χ χ' g : ℤ) • a) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [Pi.sub_apply, Pi.add_apply, chiCocycle_apply, d₁₂_hom_apply, map_zsmul, ha]
  rw [← add_smul, ← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  have h1 := chiVal_add_chiVal χ g h
  have h2 := chiVal_add_chiVal χ' g h
  have h3 := chiVal_add_chiVal (χ * χ') g h
  have h4 := chiVal_mul_hom χ χ' g
  have h5 := chiVal_mul_hom χ χ' h
  have h6 := chiVal_mul_hom χ χ' (g * h)
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have key : (N : ℤ) * (chiCarry (χ * χ') g h : ℤ) =
      (N : ℤ) * ((chiCarry χ g h : ℤ) + chiCarry χ' g h -
        ((chiCorr χ χ' h : ℤ) - chiCorr χ χ' (g * h) + chiCorr χ χ' g)) := by
    zify at h1 h2 h3 h4 h5 h6
    linear_combination h1 + h2 + h6 - h3 - h4 - h5
  exact mul_left_cancel₀ hN key

theorem H2π_chiCocycle_mul (χ χ' : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) (h : chiCocycle (χ * χ') a ∈ cocycles₂ A)
    (h₁ : chiCocycle χ a ∈ cocycles₂ A) (h₂ : chiCocycle χ' a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle (χ * χ') a, h⟩ = (H2π A).hom ⟨chiCocycle χ a, h₁⟩ + (H2π A).hom ⟨chiCocycle χ' a, h₂⟩ := by
  rw [← map_add, H2π_eq_iff]
  refine ⟨-(fun g => (chiCorr χ χ' g : ℤ) • a), ?_⟩
  rw [map_neg]
  change _ = chiCocycle (χ * χ') a - (chiCocycle χ a + chiCocycle χ' a)
  rw [chiCocycle_mul_eq χ χ' a ha]
  abel

theorem H2π_chiCocycle_one {A : Rep ℤ G} (a : A) (h : chiCocycle (1 : G →* Multiplicative (ZMod N)) a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle (1 : G →* Multiplicative (ZMod N)) a, h⟩ = 0 := by
  rw [H2π_eq_zero_iff]
  refine ⟨0, ?_⟩
  rw [map_zero]
  change (0 : G × G → A) = chiCocycle 1 a
  rw [chiCocycle_one]

theorem H2π_chiCocycle_congr {χ χ' : G →* Multiplicative (ZMod N)} (hχ : χ = χ') {A : Rep ℤ G} (a : A)
    (h : chiCocycle χ a ∈ cocycles₂ A) (h' : chiCocycle χ' a ∈ cocycles₂ A) :
    (H2π A).hom ⟨chiCocycle χ a, h⟩ = (H2π A).hom ⟨chiCocycle χ' a, h'⟩ := by
  subst hχ; rfl

theorem H2π_chiCocycle_pow (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (a : A)
    (ha : ∀ g : G, A.ρ g a = a) (i : ℕ) :
    (H2π A).hom ⟨chiCocycle (χ ^ i) a, chiCocycle_mem_cocycles₂ _ a ha⟩ =
      i • (H2π A).hom ⟨chiCocycle χ a, chiCocycle_mem_cocycles₂ _ a ha⟩ := by
  induction i with
  | zero =>
    rw [zero_smul]
    exact (H2π_chiCocycle_congr (pow_zero χ) a _ (chiCocycle_mem_cocycles₂ _ a ha)).trans
      (H2π_chiCocycle_one (N := N) a _)
  | succ i ih =>
    rw [succ_nsmul, ← ih, ← H2π_chiCocycle_mul (χ ^ i) χ a ha (chiCocycle_mem_cocycles₂ _ a ha)]
    exact H2π_chiCocycle_congr (pow_succ χ i) a _ _

end Chi

section ChiOf
variable {G : Type} [Group G] {N : ℕ} [NeZero N]

theorem cyclicLog_spec {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g : Q) : t ^ cyclicLog t ht htfin g = g := by
  unfold cyclicLog
  have := pow_finEquivZPowers_symm_apply htfin ⟨g, ht g⟩
  simpa using this

theorem cyclicLog_lt {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g : Q) : cyclicLog t ht htfin g < orderOf t :=
  ((finEquivZPowers htfin).symm ⟨g, ht g⟩).isLt

theorem cyclicLog_mul_modEq {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (g h : Q) : cyclicLog t ht htfin (g * h) ≡ cyclicLog t ht htfin g + cyclicLog t ht htfin h [MOD orderOf t] := by
  rw [← pow_eq_pow_iff_modEq, pow_add, cyclicLog_spec, cyclicLog_spec, cyclicLog_spec]

theorem cyclicLog_one {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t) :
    cyclicLog t ht htfin 1 = 0 := by
  have h2 := cyclicLog_lt t ht htfin 1
  have h1 : t ^ cyclicLog t ht htfin 1 = t ^ 0 := by rw [pow_zero]; exact cyclicLog_spec t ht htfin 1
  rw [pow_eq_pow_iff_modEq, Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt h2] at h1
  exact h1

noncomputable def chiOf (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) : G →* Multiplicative (ZMod N) where
  toFun g := Multiplicative.ofAdd (((N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g) : ℕ) : ZMod N)
  map_one' := by
    simp only [QuotientGroup.mk_one, cyclicLog_one, mul_zero, Nat.cast_zero, ofAdd_zero]
  map_mul' g h := by
    rw [← ofAdd_add, ← Nat.cast_add, QuotientGroup.mk_mul]
    congr 1
    rw [ZMod.natCast_eq_natCast_iff, ← mul_add]
    have := (cyclicLog_mul_modEq t ht htfin (QuotientGroup.mk g) (QuotientGroup.mk h)).mul_left' (N / orderOf t)
    rwa [Nat.div_mul_cancel hN] at this

theorem chiVal_chiOf (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) :
    chiVal (chiOf S t ht htfin hN) g = (N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g) := by
  simp only [chiVal, chiOf, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  calc (N / orderOf t) * cyclicLog t ht htfin (QuotientGroup.mk g)
      < (N / orderOf t) * orderOf t :=
        (Nat.mul_lt_mul_left (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hN) htfin.orderOf_pos)).mpr
          (cyclicLog_lt t ht htfin _)
    _ = N := Nat.div_mul_cancel hN

theorem chiOf_apply_mk_eq (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) (i : ℕ) (hi : (QuotientGroup.mk g : G ⧸ S) = t ^ i) :
    chiOf S t ht htfin hN g = Multiplicative.ofAdd (((N / orderOf t) * i : ℕ) : ZMod N) := by
  simp only [chiOf, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [ZMod.natCast_eq_natCast_iff]
  have h1 : t ^ cyclicLog t ht htfin (QuotientGroup.mk g) = t ^ i := by rw [cyclicLog_spec]; exact hi
  rw [pow_eq_pow_iff_modEq] at h1
  have := h1.mul_left' (N / orderOf t)
  rwa [Nat.div_mul_cancel hN] at this

theorem le_chiVal_add_iff (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g h : G) :
    N ≤ chiVal (chiOf S t ht htfin hN) g + chiVal (chiOf S t ht htfin hN) h ↔
      orderOf t ≤ cyclicLog t ht htfin (QuotientGroup.mk g) + cyclicLog t ht htfin (QuotientGroup.mk h) := by
  rw [chiVal_chiOf, chiVal_chiOf, ← mul_add]
  have hpos : 0 < N / orderOf t := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hN) htfin.orderOf_pos
  constructor
  · intro hle
    by_contra hlt
    push Not at hlt
    have := (Nat.mul_lt_mul_left hpos).mpr hlt
    rw [Nat.div_mul_cancel hN] at this
    omega
  · intro hle
    calc N = (N / orderOf t) * orderOf t := (Nat.div_mul_cancel hN).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hle

theorem inf_H2π_carryFun_eq (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) {A : Rep ℤ G} (x : A.quotientToInvariants S)
    (hc : carryFun t ht htfin x ∈ cocycles₂ (A.quotientToInvariants S))
    (hc' : chiCocycle (chiOf S t ht htfin hN) (x.1 : A) ∈ cocycles₂ A) :
    ((infNatTrans ℤ S 2).app A).hom ((H2π (A.quotientToInvariants S)).hom ⟨carryFun t ht htfin x, hc⟩) =
      (H2π A).hom ⟨chiCocycle (chiOf S t ht htfin hN) (x.1 : A), hc'⟩ := by
  rw [infNatTrans_app]
  change (H2π _ ≫ map _ _ 2).hom _ = _
  rw [H2π_comp_map]
  change (H2π A).hom (mapCocycles₂ _ _ _) = _
  congr 1
  apply cocycles₂_ext
  intro g h
  rw [coe_mapCocycles₂]
  change (carryFun t ht htfin x (QuotientGroup.mk g, QuotientGroup.mk h)).1 = chiCocycle (chiOf S t ht htfin hN) x.1 (g, h)
  simp only [carryFun, chiCocycle, le_chiVal_add_iff]
  split_ifs <;> rfl

end ChiOf

section P4
variable {G : Type} [Group G] {N : ℕ} [NeZero N]

theorem chiOf_eq_one_of_mem (S : Subgroup G) [S.Normal] (t : G ⧸ S) (ht : ∀ g : G ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (hN : orderOf t ∣ N) (g : G) (hg : g ∈ S) : chiOf S t ht htfin hN g = 1 := by
  have : (QuotientGroup.mk g : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  simp only [chiOf, MonoidHom.coe_mk, OneHom.coe_mk, this, cyclicLog_one, mul_zero, Nat.cast_zero, ofAdd_zero]

theorem exists_eq_natCast_div_mul {d : ℕ} (hd : d ∣ N) (hd0 : 0 < d) (w : ZMod N) (hw : d • w = 0) :
    ∃ i : ℕ, w = ((N / d * i : ℕ) : ZMod N) := by
  have h1 : ((d * w.val : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hw]
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨e, he⟩ := hd
  have hNd : N / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
  obtain ⟨k, hk⟩ := h1
  have h2 : d * e ∣ d * w.val := ⟨k, by rw [hk, he]⟩
  obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_left hd0 h2
  refine ⟨i, ?_⟩
  rw [hNd, ← hi, ZMod.natCast_zmod_val]

variable [Finite G]

theorem exists_chiOf_eq (χ : G →* Multiplicative (ZMod N)) :
    ∃ (t : G ⧸ χ.ker) (ht : ∀ g : G ⧸ χ.ker, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
      (hN : orderOf t ∣ N), χ = chiOf χ.ker t ht htfin hN := by
  classical
  set d := Nat.card (G ⧸ χ.ker) with hd
  have hd0 : 0 < d := Nat.card_pos
  have hN0 : N ≠ 0 := NeZero.ne N

  have hdN : d ∣ N := by
    have h1 : d = Nat.card χ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv
    rw [h1]
    have := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod N)), Fintype.card_multiplicative, ZMod.card] at this

  have hval : ∀ g : G, ∃ i : ℕ, χ g = Multiplicative.ofAdd ((N / d * i : ℕ) : ZMod N) := by
    intro g
    have hgd : χ g ^ d = 1 := by
      rw [← map_pow, ← QuotientGroup.kerLift_mk, QuotientGroup.mk_pow, pow_card_eq_one', map_one]
    obtain ⟨i, hi⟩ := exists_eq_natCast_div_mul hdN hd0 (Multiplicative.toAdd (χ g))
      (by rw [← toAdd_pow, hgd, toAdd_one])
    exact ⟨i, by rw [← hi, ofAdd_toAdd]⟩

  set z : Multiplicative (ZMod N) := Multiplicative.ofAdd ((N / d : ℕ) : ZMod N) with hz
  have hzord : orderOf z = d := by
    rw [hz, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe _ hN0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdN),
      Nat.div_div_self hdN hN0]
  have hrange : χ.range = Subgroup.zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨g, rfl⟩
      obtain ⟨i, hi⟩ := hval g
      refine ⟨(i : ℤ), ?_⟩
      change z ^ (i : ℤ) = χ g
      rw [zpow_natCast, hi, hz, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm]
    · rw [Nat.card_zpowers, hzord]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv).le
  have hzmem : z ∈ χ.range := by rw [hrange]; exact Subgroup.mem_zpowers z
  obtain ⟨g₁, hg₁⟩ := hzmem

  set t : G ⧸ χ.ker := QuotientGroup.mk g₁ with htdef
  have htord : orderOf t = d := by
    rw [← orderOf_injective (QuotientGroup.kerLift χ) (QuotientGroup.kerLift_injective χ) t, htdef,
      QuotientGroup.kerLift_mk, hg₁, hzord]
  have htop : Subgroup.zpowers t = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, htord]
  have ht : ∀ g : G ⧸ χ.ker, g ∈ Subgroup.zpowers t := fun g => by rw [htop]; exact Subgroup.mem_top g
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  refine ⟨t, ht, htfin, htord ▸ hdN, ?_⟩
  ext g
  have hj := cyclicLog_spec t ht htfin (QuotientGroup.mk g)
  set j := cyclicLog t ht htfin (QuotientGroup.mk g)
  rw [chiOf_apply_mk_eq χ.ker t ht htfin (htord ▸ hdN) g j hj.symm, htord]

  have hmem : (g₁ ^ j)⁻¹ * g ∈ χ.ker := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, ← htdef, hj]
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hg₁, inv_mul_eq_one] at hmem
  rw [← hmem, hz, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm]

end P4

theorem sum_range_orderOf_eq_sum {Q : Type} [Group Q] [Fintype Q] {X : Type} [AddCommMonoid X]
    (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t) (f : Q → X) :
    ∑ i ∈ Finset.range (orderOf t), f (t ^ i) = ∑ c : Q, f c := by
  classical
  rw [Finset.sum_range (fun i => f (t ^ i))]

  have htop : Subgroup.zpowers t = ⊤ := by
    rw [eq_top_iff]; intro g _; exact ht g
  let e : Fin (orderOf t) ≃ Q :=
    (finEquivZPowers htfin).trans ((MulEquiv.subgroupCongr htop).toEquiv.trans Subgroup.topEquiv.toEquiv)
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  congr 1

theorem coe_qti_ρ_mk {H : Type} [Group H] {Mu : Type} [CommGroup Mu] [MulDistribMulAction H Mu]
    (S : Subgroup H) [S.Normal] (g : H) (b : (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) :
    ((((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S).ρ (QuotientGroup.mk g) b).1 : Additive Mu) =
      Additive.ofMul (g • Additive.toMul (α := Mu) b.1) := by
  change ((Representation.ofQuotient ((Rep.ofMulDistribMulAction H Mu).ρ.toInvariants S) S (g : H ⧸ S) b).1 : Additive Mu) = _
  rw [Representation.ofQuotient_coe_apply]
  rfl

theorem coe_qti_ρ {H : Type} [Group H] {Mu : Type} [CommGroup Mu] [MulDistribMulAction H Mu]
    (S : Subgroup H) [S.Normal] (c : H ⧸ S) (b : (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) :
    ((((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S).ρ c b).1 : Additive Mu) =
      Additive.ofMul (c.out • Additive.toMul (α := Mu) b.1) := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  exact coe_qti_ρ_mk S _ b

theorem exists_norm_of_carry_eq_zero {H : Type} [Group H] [Finite H] {Mu : Type} [CommGroup Mu]
    [MulDistribMulAction H Mu] (S : Subgroup H) [S.Normal] (t : H ⧸ S) (ht : ∀ g : H ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (m : Mu) (hm : ∀ h : H, h • m = m)
    (hmS : (Additive.ofMul m : Rep.ofMulDistribMulAction H Mu) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H Mu).ρ.comp S.subtype))
    (hc : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) ⟨Additive.ofMul m, hmS⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S))
    (h0 : (H2π ((Rep.ofMulDistribMulAction H Mu).quotientToInvariants S)).hom
      ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H Mu).quotientToInvariants S) ⟨Additive.ofMul m, hmS⟩, hc⟩ = 0) :
    ∃ b : Mu, (∀ h ∈ S, h • b = b) ∧ ∏ᶠ c : H ⧸ S, (Quotient.out c) • b = m := by
  classical
  letI : Fintype (H ⧸ S) := Fintype.ofFinite _
  set A := Rep.ofMulDistribMulAction H Mu
  have hfix : (A.quotientToInvariants S).ρ t ⟨Additive.ofMul m, hmS⟩ = ⟨Additive.ofMul m, hmS⟩ := by
    induction t using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      rw [coe_qti_ρ_mk]
      change Additive.ofMul (g • m) = Additive.ofMul m
      rw [hm]
  obtain ⟨b, hb⟩ := (groupCohomology.carry_H2pi_eq_zero_iff t ht htfin _ hfix hc).1 h0
  refine ⟨Additive.toMul (α := Mu) b.1, fun h hh => ?_, ?_⟩
  · have := b.2 ⟨h, hh⟩
    change A.ρ h b.1 = b.1 at this
    exact congrArg Additive.toMul this
  · rw [finprod_eq_prod_of_fintype]
    apply_fun Additive.ofMul using Additive.ofMul.injective
    rw [ofMul_prod, ← sum_range_orderOf_eq_sum t ht htfin
      (fun c => Additive.ofMul (Quotient.out c • Additive.toMul (α := Mu) b.1))]
    have hb1 := congrArg (fun y : A.quotientToInvariants S => (y.1 : Additive Mu)) hb
    simp only [AddSubmonoidClass.coe_finsetSum] at hb1
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hb1
    rw [coe_qti_ρ]

theorem zmultiples_eq_top_of_card_le {X : Type} [AddCommGroup X] [Finite X] (u : X) (n : ℕ)
    (hcard : Nat.card X ≤ n) (hu : ∀ c : ℤ, c • u = 0 → (n : ℤ) ∣ c) :
    AddSubgroup.zmultiples u = ⊤ ∧ addOrderOf u = n := by
  have hfin : IsOfFinAddOrder u := isOfFinAddOrder_of_finite u
  have ho : 0 < addOrderOf u := hfin.addOrderOf_pos
  have hdvd : (n : ℤ) ∣ (addOrderOf u : ℤ) := hu _ (by rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero u)
  have hle : n ≤ addOrderOf u := Nat.le_of_dvd ho (by exact_mod_cast hdvd)
  have hcardz : Nat.card (AddSubgroup.zmultiples u) = addOrderOf u := Nat.card_zmultiples u
  have hsub : Nat.card (AddSubgroup.zmultiples u) ≤ Nat.card X :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have heq : Nat.card (AddSubgroup.zmultiples u) = Nat.card X := by omega
  refine ⟨AddSubgroup.eq_top_of_card_eq _ heq, by omega⟩

section FC

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    [MulDistribMulAction H (↥M)ˣ]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]

theorem isSolvable_H : Group.IsSolvable H := Group.isSolvable_of_comm (fun a b => (IsMulCommutative.is_comm).comm a b)

theorem dvd_of_zsmul_eq_zero
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (c : ℤ) (hc : c • u = 0) : (Nat.card H : ℤ) ∣ c := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (⊤ : Subgroup H) := Fintype.ofFinite _
  obtain ⟨-, h2, h3⟩ := ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
    q M H hH hcompat (isSolvable_H H) K hK u hu
  set r := (map (⊤ : Subgroup H).subtype (𝟙 (Rep.res (⊤ : Subgroup H).subtype (Rep.ofMulDistribMulAction H (↥M)ˣ))) 2).hom
  have hy : AddSubgroup.zmultiples (r u) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span ℤ {r u} := by rw [h3 ⊤]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨a, by rw [← ha]; exact (int_smul_eq_zsmul _ a (r u)).symm⟩
  have hcard : addOrderOf (r u) = Nat.card H := by
    rw [← Nat.card_zmultiples, hy, AddSubgroup.card_top, h2 ⊤]
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toEquiv
  have : c • r u = 0 := by rw [← map_zsmul, hc, map_zero]
  rw [← hcard]
  exact_mod_cast (addOrderOf_dvd_iff_zsmul_eq_zero.mpr this)

theorem zmultiples_fc_eq_top
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u) :
    AddSubgroup.zmultiples u = ⊤ ∧ addOrderOf u = Nat.card H := by
  obtain ⟨hfin, hle⟩ := ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable q M H (isSolvable_H H) hH hcompat
  haveI := hfin
  exact zmultiples_eq_top_of_card_le u (Nat.card H) hle (dvd_of_zsmul_eq_zero q M H K hH hcompat hK u hu)

theorem exists_eq_nsmul_fc
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) : ∃ c : ℕ, x = c • u := by
  obtain ⟨htop, hord⟩ := zmultiples_fc_eq_top q M H K hH hcompat hK u hu
  have hx : x ∈ AddSubgroup.zmultiples u := by rw [htop]; trivial
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  refine ⟨(k % (Nat.card H : ℤ)).toNat, ?_⟩
  have h0 : 0 ≤ k % (Nat.card H : ℤ) := Int.emod_nonneg _ (by exact_mod_cast Nat.card_pos.ne')
  rw [← hk, ← natCast_zsmul, Int.toNat_of_nonneg h0, ← hord, mod_addOrderOf_zsmul]

end FC

noncomputable section

section FixedLevel
variable {q : ℕ} [Fact q.Prime]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)}
    {H : Type} [Group H] [MulSemiringAction H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    (Nn : Subgroup H)

def fixedLevelIn : IntermediateField ℚ_[q] M :=
  (FixedPoints.subfield Nn M).toIntermediateField (fun x n => hH n x)

def fixedLevel : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.lift (fixedLevelIn hH Nn)

theorem fixedLevel_le : fixedLevel hH Nn ≤ M := IntermediateField.lift_le _

theorem mem_fixedLevel_iff (x : M) : (x : PadicAlgCl q) ∈ fixedLevel hH Nn ↔ ∀ h ∈ Nn, h • x = x := by
  rw [fixedLevel, IntermediateField.mem_lift]
  change (∀ n : Nn, n • x = x) ↔ _
  exact ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n n.2⟩

variable {hH Nn} in

def toM (z : fixedLevel hH Nn) : M := ⟨z.1, fixedLevel_le hH Nn z.2⟩

@[scoped simp] theorem coe_toM (z : fixedLevel hH Nn) : ((toM z : M) : PadicAlgCl q) = (z : PadicAlgCl q) := rfl

theorem smul_toM (z : fixedLevel hH Nn) (n : H) (hn : n ∈ Nn) : n • toM z = toM z :=
  (mem_fixedLevel_iff hH Nn (toM z)).1 z.2 n hn

theorem toM_injective : Function.Injective (toM (hH := hH) (Nn := Nn)) := fun z w h =>
  Subtype.ext (congrArg (fun y : M => (y : PadicAlgCl q)) h)

@[scoped simp] theorem toM_add (z w : fixedLevel hH Nn) : toM (z + w) = toM z + toM w := rfl
@[scoped simp] theorem toM_mul (z w : fixedLevel hH Nn) : toM (z * w) = toM z * toM w := rfl
@[scoped simp] theorem toM_zero : toM (0 : fixedLevel hH Nn) = 0 := rfl
@[scoped simp] theorem toM_one : toM (1 : fixedLevel hH Nn) = 1 := rfl

variable [Nn.Normal]

def act (h : H) (z : fixedLevel hH Nn) : fixedLevel hH Nn :=
  ⟨((h • toM z : M) : PadicAlgCl q), by
    rw [mem_fixedLevel_iff]
    intro n hn
    rw [← mul_smul, show n * h = h * (h⁻¹ * n * h) by group, mul_smul,
      smul_toM hH Nn z _ (Subgroup.Normal.conj_mem' ‹Nn.Normal› n hn h)]⟩

@[scoped simp] theorem toM_act (h : H) (z : fixedLevel hH Nn) : toM (act hH Nn h z) = h • toM z := rfl

theorem act_one (z : fixedLevel hH Nn) : act hH Nn 1 z = z := toM_injective hH Nn (by simp)
theorem act_mul (g h : H) (z : fixedLevel hH Nn) : act hH Nn (g * h) z = act hH Nn g (act hH Nn h z) :=
  toM_injective hH Nn (by simp [mul_smul])
theorem act_of_mem (n : H) (hn : n ∈ Nn) (z : fixedLevel hH Nn) : act hH Nn n z = z :=
  toM_injective hH Nn (by simp [smul_toM hH Nn z n hn])

scoped instance quotSMul : SMul (H ⧸ Nn) (fixedLevel hH Nn) := ⟨fun c z => act hH Nn c.out z⟩

theorem mk_smul (h : H) (z : fixedLevel hH Nn) : (QuotientGroup.mk h : H ⧸ Nn) • z = act hH Nn h z := by
  change act hH Nn (QuotientGroup.mk h : H ⧸ Nn).out z = _
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul Nn h
  rw [hn, act_mul, act_of_mem hH Nn _ n.2]

theorem toM_mk_smul (h : H) (z : fixedLevel hH Nn) : toM ((QuotientGroup.mk h : H ⧸ Nn) • z) = h • toM z := by
  rw [mk_smul]; rfl

scoped instance quotAction : MulSemiringAction (H ⧸ Nn) (fixedLevel hH Nn) where
  one_smul z := by
    rw [← QuotientGroup.mk_one, mk_smul, act_one]
  mul_smul c d z := by
    induction c using QuotientGroup.induction_on with
    | H g => induction d using QuotientGroup.induction_on with
      | H h => rw [← QuotientGroup.mk_mul, mk_smul, mk_smul, mk_smul, act_mul]
  smul_zero c := by
    induction c using QuotientGroup.induction_on with
    | H g => exact toM_injective hH Nn (by rw [toM_mk_smul]; simp)
  smul_add c z w := by
    induction c using QuotientGroup.induction_on with
    | H g => exact toM_injective hH Nn (by simp only [toM_mk_smul, toM_add, smul_add])
  smul_one c := by
    induction c using QuotientGroup.induction_on with
    | H g => exact toM_injective hH Nn (by rw [toM_mk_smul]; simp)
  smul_mul c z w := by
    induction c using QuotientGroup.induction_on with
    | H g => exact toM_injective hH Nn (by simp only [toM_mk_smul, toM_mul, MulSemiringAction.smul_mul])

theorem quot_smul_algebraMap (c : H ⧸ Nn) (x : ℚ_[q]) :
    c • algebraMap ℚ_[q] (fixedLevel hH Nn) x = algebraMap ℚ_[q] (fixedLevel hH Nn) x := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    apply toM_injective hH Nn
    rw [toM_mk_smul]
    exact hH g x

end FixedLevel

section Faithful
variable {q : ℕ} [Fact q.Prime]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)}
    {H : Type} [Group H] [MulSemiringAction H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    (Nn : Subgroup H) [Nn.Normal] [Finite H] [FaithfulSMul H M]

theorem mem_of_forall_smul_eq (h : H) (hfix : ∀ x : M, (∀ n ∈ Nn, n • x = x) → h • x = x) : h ∈ Nn := by
  haveI : IsGalois (FixedPoints.subfield H M) M := ⟨⟩
  let e := FixedPoints.toAlgAutMulEquiv H M
  let NnA : Subgroup (M ≃ₐ[FixedPoints.subfield H M] M) := Nn.map e.toMonoidHom
  have h1 : e h ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField NnA) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    change h • x = x
    apply hfix
    intro n hn
    exact hx (e n) ⟨n, hn, rfl⟩
  rw [IntermediateField.fixingSubgroup_fixedField NnA] at h1
  obtain ⟨n, hn, hne⟩ := h1
  rwa [← e.injective hne]

scoped instance quotFaithful : FaithfulSMul (H ⧸ Nn) (fixedLevel hH Nn) where
  eq_of_smul_eq_smul {c d} hcd := by
    induction c using QuotientGroup.induction_on with
    | H g => induction d using QuotientGroup.induction_on with
      | H g' =>
        rw [QuotientGroup.eq]
        apply mem_of_forall_smul_eq (M := M) Nn
        intro x hx
        have hz := hcd ⟨(x : PadicAlgCl q), (mem_fixedLevel_iff hH Nn x).2 hx⟩
        have := congrArg toM hz
        rw [toM_mk_smul, toM_mk_smul] at this
        change g • x = g' • x at this
        rw [mul_smul, ← this, ← mul_smul, inv_mul_cancel, one_smul]

scoped instance quotUnitsAction : MulDistribMulAction (H ⧸ Nn) (fixedLevel hH Nn)ˣ where
  smul c v := Units.map (MulSemiringAction.toRingHom (H ⧸ Nn) (fixedLevel hH Nn) c).toMonoidHom v
  one_smul v := Units.ext (one_smul _ (v : fixedLevel hH Nn))
  mul_smul c d v := Units.ext (mul_smul c d (v : fixedLevel hH Nn))
  smul_mul c v w := Units.ext (smul_mul' c (v : fixedLevel hH Nn) (w : fixedLevel hH Nn))
  smul_one c := Units.ext (smul_one c : c • (1 : fixedLevel hH Nn) = 1)

theorem quot_coe_smul_units (c : H ⧸ Nn) (v : (fixedLevel hH Nn)ˣ) :
    ((c • v : (fixedLevel hH Nn)ˣ) : fixedLevel hH Nn) = c • (v : fixedLevel hH Nn) := rfl

theorem isBase_fixedLevel (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (hK : IsBase q M H K) :
    IsBase q (fixedLevel hH Nn) (H ⧸ Nn) K where
  le := fun y hy => (mem_fixedLevel_iff hH Nn ⟨y, hK.le hy⟩).2 (fun h _ => (hK.mem_iff ⟨y, hK.le hy⟩).1 hy h)
  mem_iff := fun z => by
    rw [show (z : PadicAlgCl q) = ((toM z : M) : PadicAlgCl q) from rfl, hK.mem_iff]
    constructor
    · intro h c
      induction c using QuotientGroup.induction_on with
      | H g => exact toM_injective hH Nn (by rw [toM_mk_smul]; exact h g)
    · intro h g
      have := congrArg toM (h (QuotientGroup.mk g))
      rwa [toM_mk_smul] at this

end Faithful

section Anchor

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (Nn : Subgroup H) [Nn.Normal] (φ : H) (π : (↥M)ˣ)
    (hzp : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ))
    (hfrob : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (hπH : ∀ h : H, h • π = π) (hπ1 : ‖((π : M) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖)

theorem isSolvable_of_isMulCommutative : Group.IsSolvable H :=
  Group.isSolvable_of_comm (fun a b => (IsMulCommutative.is_comm).comm a b)

include hcompat hK hzp hfrob hπH hπ1 hπmax in

theorem datum_fixedLevel :
    IsUnramOverlayerDatum q (fixedLevel hH Nn) (H ⧸ Nn) K M (fixedLevel_le hH Nn) H Nn Nn
      (MulEquiv.refl (H ⧸ Nn)) φ π where
  smul_algebraMap := hH
  coe_smul_units := hcompat
  mem_base_iff := hK.mem_iff
  mem_layer_iff := mem_fixedLevel_iff hH Nn
  coe_smul_eq g h hgh x := by
    rw [MulEquiv.refl_apply] at hgh
    rw [← hgh]
    change ((toM ((QuotientGroup.mk h : H ⧸ Nn) • x) : M) : PadicAlgCl q) = _
    rw [toM_mk_smul]
    rfl
  card_quotient := rfl
  mem_zpowers := hzp
  frobenius := hfrob
  smul_pi := hπH
  pi_mem := (hK.mem_iff (π : M)).2 (fun h => by rw [← hcompat, hπH])
  norm_pi_lt := hπ1
  norm_le_norm_pi := hπmax

def inclUnits : (fixedLevel hH Nn)ˣ →* (↥M)ˣ :=
  Units.map (IntermediateField.inclusion (fixedLevel_le hH Nn)).toRingHom.toMonoidHom

theorem coe_inclUnits (v : (fixedLevel hH Nn)ˣ) : ((inclUnits q M H hH Nn v : (↥M)ˣ) : M) = toM (v : fixedLevel hH Nn) := rfl

include hcompat in

def iota : Rep.res ((MulEquiv.refl (H ⧸ Nn)).symm.toMonoidHom.comp (QuotientGroup.mk' Nn))
      (Rep.ofMulDistribMulAction (H ⧸ Nn) (fixedLevel hH Nn)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (MonoidHom.toAdditive (inclUnits q M H hH Nn)).toIntLinearMap (fun h v => by
      change Additive.ofMul (inclUnits q M H hH Nn (Additive.toMul
          ((Rep.ofMulDistribMulAction (H ⧸ Nn) (fixedLevel hH Nn)ˣ).ρ (QuotientGroup.mk h) v))) =
        (Rep.ofMulDistribMulAction H (↥M)ˣ).ρ h (Additive.ofMul (inclUnits q M H hH Nn (Additive.toMul v)))
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
      congr 1
      apply Units.ext
      rw [hcompat]
      change toM ((((QuotientGroup.mk h : H ⧸ Nn) • Additive.toMul (α := (fixedLevel hH Nn)ˣ) v : (fixedLevel hH Nn)ˣ)) :
          fixedLevel hH Nn) = h • toM ((Additive.toMul (α := (fixedLevel hH Nn)ˣ) v : (fixedLevel hH Nn)ˣ) : fixedLevel hH Nn)
      rw [quot_coe_smul_units, toM_mk_smul]))

theorem iota_hom_apply (v : (fixedLevel hH Nn)ˣ) :
    Additive.toMul ((iota q M H hH hcompat Nn).hom (Additive.ofMul v)) = inclUnits q M H hH Nn v := rfl

include hH hcompat hK hzp hfrob hπH hπ1 hπmax hu in

theorem inf_carry_pi_eq_card_smul (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
    (hπNn : (Additive.ofMul π : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp Nn.subtype))
    (hc : carryFun (QuotientGroup.mk' Nn φ) hzp hfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)
        ⟨Additive.ofMul π, hπNn⟩ ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)) :
    ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
          ⟨carryFun (QuotientGroup.mk' Nn φ) hzp hfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)
            ⟨Additive.ofMul π, hπNn⟩, hc⟩) =
      Nat.card Nn • u := by
  haveI : Group.IsSolvable H := isSolvable_of_isMulCommutative H
  haveI : Group.IsSolvable (H ⧸ Nn) := inferInstance
  haveI : FiniteDimensional ℚ_[q] (fixedLevel hH Nn) :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv (fixedLevelIn hH Nn)).toLinearEquiv
  obtain ⟨u', hu', -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q (fixedLevel hH Nn) (H ⧸ Nn)
    (quot_smul_algebraMap hH Nn) (quot_coe_smul_units hH Nn) inferInstance K (isBase_fixedLevel hH Nn K hK)
  have d := datum_fixedLevel q M H hH hcompat K hK Nn φ π hzp hfrob hπH hπ1 hπmax
  have hι : ∀ v : (fixedLevel hH Nn)ˣ, (((Additive.toMul ((iota q M H hH hcompat Nn).hom (Additive.ofMul v)) : (↥M)ˣ) : M) :
      PadicAlgCl q) = ((v : fixedLevel hH Nn) : PadicAlgCl q) := fun v => rfl
  have e1 := hu' M (fixedLevel_le hH Nn) H Nn Nn (MulEquiv.refl (H ⧸ Nn)) φ π d (iota q M H hH hcompat Nn) hι hfin hc
  have e2 := ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass q M H hH hcompat inferInstance K hK
    (fixedLevel hH Nn) (fixedLevel_le hH Nn) (H ⧸ Nn) (quot_coe_smul_units hH Nn) Nn (MulEquiv.refl (H ⧸ Nn))
    (mem_fixedLevel_iff hH Nn) d.coe_smul_eq u' hu' u hu (iota q M H hH hcompat Nn) hι
  rw [← e2, e1]
  rfl

end Anchor

end

variable (q : ℕ) [Fact q.Prime]

theorem mem_Rw_iff_norm_le (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (x : K) :
    x ∈ Rw q K ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  change algebraMap K (PadicAlgCl q) x ∈ padicIntegers q ↔ _
  rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  rfl

theorem val_eq_one_iff_norm_eq_one (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (v : (↥K)ˣ →* Multiplicative ℤ)
    (hv : ∀ x : (↥K)ˣ, v x = 1 ↔ ((x : K) ∈ Rw q K ∧ ((x⁻¹ : (↥K)ˣ) : K) ∈ Rw q K))
    (x : (↥K)ˣ) : v x = 1 ↔ ‖((x : K) : PadicAlgCl q)‖ = 1 := by
  rw [hv, mem_Rw_iff_norm_le, mem_Rw_iff_norm_le]
  have hx0 : ((x : K) : PadicAlgCl q) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true]
  have hinv : (((x⁻¹ : (↥K)ˣ) : K) : PadicAlgCl q) = (((x : K) : PadicAlgCl q))⁻¹ := by
    rw [Units.val_inv_eq_inv_val]; rfl
  rw [hinv, norm_inv]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < ‖((x : K) : PadicAlgCl q)‖ := norm_pos_iff.mpr hx0
    have := (inv_le_one₀ hpos).mp h2
    linarith
  · intro h
    rw [h, inv_one]
    exact ⟨le_refl _, le_refl _⟩

theorem norm_eq_norm_of_val_eq (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (v : (↥K)ˣ →* Multiplicative ℤ)
    (hv : ∀ x : (↥K)ˣ, v x = 1 ↔ ((x : K) ∈ Rw q K ∧ ((x⁻¹ : (↥K)ˣ) : K) ∈ Rw q K))
    (x y : (↥K)ˣ) (h : v x = v y) : ‖((x : K) : PadicAlgCl q)‖ = ‖((y : K) : PadicAlgCl q)‖ := by
  have h1 : v (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [val_eq_one_iff_norm_eq_one q K v hv] at h1
  have hy0 : ‖((y : K) : PadicAlgCl q)‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true]
  have : (((x * y⁻¹ : (↥K)ˣ) : K) : PadicAlgCl q) = ((x : K) : PadicAlgCl q) * (((y : K) : PadicAlgCl q))⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  rw [this, norm_mul, norm_inv] at h1
  field_simp at h1
  linarith [h1]

theorem exists_norm_eq_norm_zpow (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (ϖ : (↥K)ˣ) (hϖ1 : ‖((ϖ : K) : PadicAlgCl q)‖ < 1)
    (hϖmax : ∀ y : K, ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((ϖ : K) : PadicAlgCl q)‖)
    (a : (↥K)ˣ) : ∃ k : ℤ, ‖((a : K) : PadicAlgCl q)‖ = ‖((ϖ : K) : PadicAlgCl q)‖ ^ k := by
  obtain ⟨v, hsurj, hv, -, -⟩ := ExtCitation.LocalLevel.exists_valuation_units_Kw q K

  set nr : (↥K)ˣ → ℝ := fun x => ‖((x : K) : PadicAlgCl q)‖ with hnr
  have nr_pos : ∀ x, 0 < nr x := fun x => norm_pos_iff.mpr (by simp)
  have nr_mul : ∀ x y, nr (x * y) = nr x * nr y := fun x y => by
    simp only [hnr, Units.val_mul]; exact norm_mul _ _
  have nr_zpow : ∀ x (k : ℤ), nr (x ^ k) = nr x ^ k := by
    intro x k
    have : (((x ^ k : (↥K)ˣ) : K) : PadicAlgCl q) = (((x : K) : PadicAlgCl q)) ^ k := by
      rw [Units.val_zpow_eq_zpow_val]
      exact map_zpow₀ (algebraMap K (PadicAlgCl q)) _ _
    simp only [hnr, this, norm_zpow]
  have nr_inv : ∀ x, nr x⁻¹ = (nr x)⁻¹ := fun x => by
    have := nr_zpow x (-1); simpa using this

  obtain ⟨ϖ₁, hϖ₁⟩ := hsurj (Multiplicative.ofAdd 1)
  have hall : ∀ x, nr x = nr ϖ₁ ^ (Multiplicative.toAdd (v x)) := by
    intro x
    have : v x = v (ϖ₁ ^ Multiplicative.toAdd (v x)) := by
      rw [map_zpow, hϖ₁, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    exact (norm_eq_norm_of_val_eq q K v hv x _ this).trans (nr_zpow _ _)
  have hne : nr ϖ₁ ≠ 1 := by
    intro h1
    have := (val_eq_one_iff_norm_eq_one q K v hv ϖ₁).2 h1
    rw [hϖ₁, ← ofAdd_zero] at this
    exact one_ne_zero (Multiplicative.ofAdd.injective this)
  set m := Multiplicative.toAdd (v ϖ) with hmdef
  have hϖm : nr ϖ = nr ϖ₁ ^ m := hall ϖ
  change nr ϖ < 1 at hϖ1
  change ∃ k : ℤ, nr a = nr ϖ ^ k
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h2 : nr ϖ₁ ≤ nr ϖ := hϖmax _ hlt
    have hm0 : 0 < m := by
      have : nr ϖ₁ ^ m < nr ϖ₁ ^ (0 : ℤ) := by rw [zpow_zero, ← hϖm]; exact hϖ1
      exact (zpow_lt_zpow_iff_right_of_lt_one₀ (nr_pos _) hlt).1 this
    have hm1 : m ≤ 1 := by
      have : nr ϖ₁ ^ (1 : ℤ) ≤ nr ϖ₁ ^ m := by rw [zpow_one, hϖm.symm]; exact h2
      exact (zpow_le_zpow_iff_right_of_lt_one₀ (nr_pos _) hlt).1 this
    have hm : m = 1 := le_antisymm hm1 (by omega)
    refine ⟨Multiplicative.toAdd (v a), ?_⟩
    rw [hϖm, hm, zpow_one]
    exact hall a
  ·
    have hlt : nr ϖ₁⁻¹ < 1 := by rw [nr_inv]; exact inv_lt_one_of_one_lt₀ hgt
    have hall' : ∀ x, nr x = nr ϖ₁⁻¹ ^ (-Multiplicative.toAdd (v x)) := by
      intro x; rw [nr_inv, inv_zpow', neg_neg]; exact hall x
    have hϖm' : nr ϖ = nr ϖ₁⁻¹ ^ (-m) := hall' ϖ
    have h2 : nr ϖ₁⁻¹ ≤ nr ϖ := hϖmax _ hlt
    have hm0 : 0 < -m := by
      have : nr ϖ₁⁻¹ ^ (-m) < nr ϖ₁⁻¹ ^ (0 : ℤ) := by rw [zpow_zero, ← hϖm']; exact hϖ1
      exact (zpow_lt_zpow_iff_right_of_lt_one₀ (nr_pos _) hlt).1 this
    have hm1 : -m ≤ 1 := by
      have : nr ϖ₁⁻¹ ^ (1 : ℤ) ≤ nr ϖ₁⁻¹ ^ (-m) := by rw [zpow_one, hϖm'.symm]; exact h2
      exact (zpow_le_zpow_iff_right_of_lt_one₀ (nr_pos _) hlt).1 this
    have hm : -m = 1 := le_antisymm hm1 (by omega)
    refine ⟨-Multiplicative.toAdd (v a), ?_⟩
    rw [hϖm', hm, zpow_one]
    exact hall' a

section MainProof

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)

scoped instance neZero_natCard_group : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩

include hcompat in
theorem ρ_ofMul_incl (a : (↥K)ˣ) (g : H) :
    (Rep.ofMulDistribMulAction H (↥M)ˣ).ρ g (Additive.ofMul (incl q M H K hK a)) = Additive.ofMul (incl q M H K hK a) := by
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  exact congrArg Additive.ofMul (smul_incl q M H hcompat K hK g a)

noncomputable def Fchi (a : (↥K)ˣ) (χ : H →* Multiplicative (ZMod (Nat.card H))) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ) :=
  (H2π (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
    ⟨chiCocycle χ (Additive.ofMul (incl q M H K hK a)), chiCocycle_mem_cocycles₂ χ _ (ρ_ofMul_incl q M H hcompat K hK a)⟩

theorem chiCocycle_add {G : Type} [Group G] {N : ℕ} (χ : G →* Multiplicative (ZMod N)) {A : Rep ℤ G} (x y : A) :
    chiCocycle χ (x + y) = chiCocycle χ x + chiCocycle χ y := by
  funext p; simp only [chiCocycle, Pi.add_apply]; split_ifs <;> simp

theorem Fchi_mul_left (a b : (↥K)ˣ) (χ : H →* Multiplicative (ZMod (Nat.card H))) :
    Fchi q M H hcompat K hK (a * b) χ = Fchi q M H hcompat K hK a χ + Fchi q M H hcompat K hK b χ := by
  unfold Fchi
  rw [← map_add]
  congr 1
  apply Subtype.ext
  change chiCocycle χ _ = chiCocycle χ _ + chiCocycle χ _
  rw [← chiCocycle_add]
  congr 1

theorem Fchi_mul_right (a : (↥K)ˣ) (χ χ' : H →* Multiplicative (ZMod (Nat.card H))) :
    Fchi q M H hcompat K hK a (χ * χ') = Fchi q M H hcompat K hK a χ + Fchi q M H hcompat K hK a χ' :=
  H2π_chiCocycle_mul χ χ' _ (ρ_ofMul_incl q M H hcompat K hK a) _ _ _

theorem Fchi_pow (a : (↥K)ˣ) (χ : H →* Multiplicative (ZMod (Nat.card H))) (i : ℕ) :
    Fchi q M H hcompat K hK a (χ ^ i) = i • Fchi q M H hcompat K hK a χ :=
  H2π_chiCocycle_pow χ _ (ρ_ofMul_incl q M H hcompat K hK a) i

theorem Fchi_one_right (a : (↥K)ˣ) : Fchi q M H hcompat K hK a 1 = 0 :=
  H2π_chiCocycle_one (N := Nat.card H) _ _

theorem Fchi_eq_of_generators (E : (↥K)ˣ →* (H →* Multiplicative (ZMod (Nat.card H))) → Multiplicative (groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)))
    (S : Set (↥K)ˣ) (hS : ∀ a ∈ S, ∀ χ, Fchi q M H hcompat K hK a χ = Multiplicative.toAdd (E a χ))
    (a : (↥K)ˣ) (ha : a ∈ Subgroup.closure S) (χ : H →* Multiplicative (ZMod (Nat.card H))) :
    Fchi q M H hcompat K hK a χ = Multiplicative.toAdd (E a χ) := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx χ
  | one =>
    rw [map_one]
    have h := Fchi_mul_left q M H hcompat K hK 1 1 χ
    rw [mul_one, left_eq_add] at h
    rw [h]; rfl
  | mul x y _ _ hx hy => rw [Fchi_mul_left, hx, hy, map_mul]; rfl
  | inv x _ hx =>
    have h := Fchi_mul_left q M H hcompat K hK x x⁻¹ χ
    have h1 := Fchi_mul_left q M H hcompat K hK 1 1 χ
    rw [mul_one, left_eq_add] at h1
    rw [mul_inv_cancel, h1] at h
    rw [map_inv]
    change _ = -Multiplicative.toAdd (E x χ)
    rw [← hx]
    exact (neg_eq_of_add_eq_zero_right h.symm).symm

end MainProof

section Key

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (Nn : Subgroup H) [Nn.Normal] (φ : H) (π : (↥M)ˣ)
    (hzp : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ))
    (hfrob : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (hπH : ∀ h : H, h • π = π) (hπ1 : ‖((π : M) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖)
    (hexp : ∀ h : H, h ^ Nn.index = 1)
    (f : (↥K)ˣ →* H)
    (h1 : ∀ (a : (↥K)ˣ) (k : ℤ), ‖((a : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖ ^ k →
      (QuotientGroup.mk (f a) : H ⧸ Nn) = (QuotientGroup.mk φ : H ⧸ Nn) ^ k)
    (h2 : ∀ (H' : Subgroup H) (a : (↥K)ˣ),
      (∃ b : (↥M)ˣ, (∀ h ∈ H', h • b = b) ∧
        ∏ᶠ c : H ⧸ H', (Quotient.out c) • b = Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) →
      f a ∈ H')

include hH hcompat hK hu in
theorem card_nsmul_fc : Nat.card H • u = 0 := by
  rw [← (zmultiples_fc_eq_top q M H K hH hcompat hK u hu).2]
  exact addOrderOf_nsmul_eq_zero u

include hH hcompat hK hu in
theorem nsmul_mod_card (k : ℕ) : (k % Nat.card H) • u = k • u := by
  conv_rhs => rw [← Nat.div_add_mod k (Nat.card H)]
  rw [add_nsmul, mul_nsmul, card_nsmul_fc q M H hH hcompat K hK u hu, nsmul_zero, zero_add]

theorem orderOf_eq_index {S : Subgroup H} [S.Normal] (t : H ⧸ S) (ht : ∀ g : H ⧸ S, g ∈ Subgroup.zpowers t) :
    orderOf t = S.index := by
  have htop : Subgroup.zpowers t = ⊤ := by rw [eq_top_iff]; intro g _; exact ht g
  rw [← Nat.card_zpowers, htop, Subgroup.card_top]
  rfl

theorem card_div_index (S : Subgroup H) : Nat.card H / S.index = Nat.card S := by
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.card_mul_index S, Nat.mul_div_cancel _ hpos]

include hcompat in
theorem quot_ρ_inclInv (S : Subgroup H) [S.Normal] (c : H ⧸ S) (a : (↥K)ˣ) :
    ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants S).ρ c (inclInv q M H hcompat K hK S a) =
      inclInv q M H hcompat K hK S a := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    rw [coe_qti_ρ_mk]
    change Additive.ofMul (g • incl q M H K hK a) = Additive.ofMul (incl q M H K hK a)
    rw [smul_incl q M H hcompat K hK g a]

include hcompat in
theorem carry_inclInv_mem (S : Subgroup H) [S.Normal] (t : H ⧸ S) (ht : ∀ g : H ⧸ S, g ∈ Subgroup.zpowers t)
    (htfin : IsOfFinOrder t) (a : (↥K)ˣ) :
    carryFun t ht htfin (inclInv q M H hcompat K hK S a) ∈
      cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants S) :=
  groupCohomology.carryFun_mem_cocycles2 t ht htfin _ (quot_ρ_inclInv q M H hcompat K hK S t a)

end Key

section Key3
variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (f : (↥K)ˣ →* H)

noncomputable def Echi : (↥K)ˣ →* ((H →* Multiplicative (ZMod (Nat.card H))) →
    Multiplicative (groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ))) where
  toFun a χ := Multiplicative.ofAdd (chiVal χ (f a) • u)
  map_one' := by
    funext χ
    rw [map_one, chiVal_one, zero_nsmul]
    rfl
  map_mul' a b := by
    funext χ
    rw [Pi.mul_apply, ← ofAdd_add, map_mul, chiVal_mul, ← add_nsmul, nsmul_mod_card q M H hH hcompat K hK u hu]

theorem toAdd_Echi (a : (↥K)ˣ) (χ : H →* Multiplicative (ZMod (Nat.card H))) :
    Multiplicative.toAdd (Echi q M H hH hcompat K hK u hu f a χ) = chiVal χ (f a) • u := rfl

end Key3

section Key2

variable (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)
    (Nn : Subgroup H) [Nn.Normal] (φ : H) (π : (↥M)ˣ)
    (hzp : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ))
    (hfrob : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (hπH : ∀ h : H, h • π = π) (hπ1 : ‖((π : M) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖)
    (hexp : ∀ h : H, h ^ Nn.index = 1)
    (f : (↥K)ˣ →* H)
    (h1 : ∀ (a : (↥K)ˣ) (k : ℤ), ‖((a : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖ ^ k →
      (QuotientGroup.mk (f a) : H ⧸ Nn) = (QuotientGroup.mk φ : H ⧸ Nn) ^ k)
    (h2 : ∀ (H' : Subgroup H) (a : (↥K)ˣ),
      (∃ b : (↥M)ˣ, (∀ h ∈ H', h • b = b) ∧
        ∏ᶠ c : H ⧸ H', (Quotient.out c) • b = Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) →
      f a ∈ H')

include hH hcompat hu hzp hfrob hπH hπ1 hπmax in

theorem Fchi_chi0_eq (hfin0 : IsOfFinOrder (QuotientGroup.mk' Nn φ)) (hN0 : orderOf (QuotientGroup.mk' Nn φ) ∣ Nat.card H)
    (ϖ : (↥K)ˣ) (hϖ : ‖((ϖ : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖) :
    Fchi q M H hcompat K hK ϖ (chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN0) = Nat.card Nn • u := by
  have hπNn : (Additive.ofMul π : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp Nn.subtype) :=
    fun n => congrArg Additive.ofMul (hπH (n : H))
  have hρπ : ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn).ρ (QuotientGroup.mk' Nn φ) ⟨Additive.ofMul π, hπNn⟩ =
      ⟨Additive.ofMul π, hπNn⟩ := by
    apply Subtype.ext
    exact (coe_qti_ρ_mk Nn φ _).trans (congrArg Additive.ofMul (hπH φ))
  have hcπ := groupCohomology.carryFun_mem_cocycles2 (QuotientGroup.mk' Nn φ) hzp hfin0 _ hρπ
  have hcϖ := carry_inclInv_mem q M H hcompat K hK Nn (QuotientGroup.mk' Nn φ) hzp hfin0 ϖ
  have step : Fchi q M H hcompat K hK ϖ (chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN0) =
      ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
          ⟨carryFun (QuotientGroup.mk' Nn φ) hzp hfin0 (inclInv q M H hcompat K hK Nn ϖ), hcϖ⟩) :=
    (inf_H2π_carryFun_eq Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN0 (inclInv q M H hcompat K hK Nn ϖ) hcϖ
      (chiCocycle_mem_cocycles₂ _ _ (ρ_ofMul_incl q M H hcompat K hK ϖ))).symm
  rw [step]
  obtain ⟨inv, hinv⟩ := ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
    q M H hH hcompat Nn φ hzp hfin0 π hπH hπ1 hπmax
  have i1 := hinv (inclInv q M H hcompat K hK Nn ϖ) 1 hcϖ (by rw [zpow_one]; exact hϖ)
  have i2 := hinv ⟨Additive.ofMul π, hπNn⟩ 1 hcπ (by rw [zpow_one]; rfl)
  have heq := inv.injective (i1.trans i2.symm)
  rw [heq]
  exact inf_carry_pi_eq_card_smul q M H hH hcompat K hK u hu Nn φ π hzp hfrob hπH hπ1 hπmax hfin0 hπNn hcπ

include hH hu hzp hfrob hπH hπ1 hπmax hexp h1 h2 in

theorem Fchi_uniformiser (ϖ : (↥K)ˣ) (hϖ : ‖((ϖ : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖)
    (χ : H →* Multiplicative (ZMod (Nat.card H))) :
    Fchi q M H hcompat K hK ϖ χ = chiVal χ (f ϖ) • u := by
  classical
  set σ := f ϖ with hσdef

  have hσ : (QuotientGroup.mk σ : H ⧸ Nn) = QuotientGroup.mk φ := by
    have := h1 ϖ 1 (by rw [zpow_one]; exact hϖ)
    rwa [zpow_one] at this

  have hfin0 : IsOfFinOrder (QuotientGroup.mk' Nn φ) := isOfFinOrder_of_finite _
  have hord0 : orderOf (QuotientGroup.mk' Nn φ) = Nn.index := orderOf_eq_index H _ hzp
  have hN0 : orderOf (QuotientGroup.mk' Nn φ) ∣ Nat.card H := by rw [hord0]; exact Nn.index_dvd_card
  have hdiv : Nat.card H / orderOf (QuotientGroup.mk' Nn φ) = Nat.card Nn := by rw [hord0]; exact card_div_index H Nn
  set χ₀ := chiOf Nn (QuotientGroup.mk' Nn φ) hzp hfin0 hN0 with hχ₀def

  have hF0 : Fchi q M H hcompat K hK ϖ χ₀ = Nat.card Nn • u :=
    Fchi_chi0_eq q M H hH hcompat K hK u hu Nn φ π hzp hfrob hπH hπ1 hπmax hfin0 hN0 ϖ hϖ

  have hχ₀σ : χ₀ σ = Multiplicative.ofAdd ((Nat.card Nn : ℕ) : ZMod (Nat.card H)) := by
    rw [hχ₀def, chiOf_apply_mk_eq Nn _ hzp hfin0 hN0 σ 1 (by rw [pow_one]; exact hσ), mul_one, hdiv]
  have hEF0 : ∀ i : ℕ, Fchi q M H hcompat K hK ϖ (χ₀ ^ i) = (i * Nat.card Nn) • u := by
    intro i; rw [Fchi_pow, hF0, mul_comm i (Nat.card Nn), mul_nsmul]
  have hval0 : ∀ i : ℕ, chiVal (χ₀ ^ i) σ • u = (i * Nat.card Nn) • u := by
    intro i
    rw [chiVal, MonoidHom.pow_apply, hχ₀σ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, ← Nat.cast_mul, ZMod.val_natCast,
      nsmul_mod_card q M H hH hcompat K hK u hu]

  obtain ⟨c, hc⟩ := exists_eq_nsmul_fc q M H K hH hcompat hK u hu (Fchi q M H hcompat K hK ϖ χ)
  have hχn : χ ^ Nn.index = 1 := by
    ext h
    rw [MonoidHom.pow_apply, ← map_pow, hexp h, map_one, MonoidHom.one_apply]
  have htors : Nn.index • Fchi q M H hcompat K hK ϖ χ = 0 := by
    rw [← Fchi_pow, hχn, Fchi_one_right]
  rw [hc, ← mul_nsmul] at htors
  have hdvd : (Nat.card H : ℤ) ∣ ((c * Nn.index : ℕ) : ℤ) :=
    dvd_of_zsmul_eq_zero q M H K hH hcompat hK u hu _ (by rw [natCast_zsmul]; exact htors)
  have hdvd' : Nat.card Nn ∣ c := by
    have h3 : Nat.card H ∣ c * Nn.index := by exact_mod_cast hdvd
    rw [← Subgroup.card_mul_index Nn] at h3
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h3
  obtain ⟨i, hi⟩ := hdvd'
  have hFeq : Fchi q M H hcompat K hK ϖ χ = Fchi q M H hcompat K hK ϖ (χ₀ ^ i) := by
    rw [hc, hi, hEF0, mul_comm]

  set χ₁ := χ * (χ₀ ^ i)⁻¹ with hχ₁def
  have hχeq : χ = χ₁ * χ₀ ^ i := by rw [hχ₁def, inv_mul_cancel_right]
  have hF1 : Fchi q M H hcompat K hK ϖ χ₁ = 0 := by
    have := Fchi_mul_right q M H hcompat K hK ϖ χ₁ (χ₀ ^ i)
    rw [← hχeq, hFeq, right_eq_add] at this
    exact this

  obtain ⟨t₁, ht₁, ht₁fin, hN₁, hχ₁⟩ := exists_chiOf_eq χ₁
  have hc₁ := carry_inclInv_mem q M H hcompat K hK χ₁.ker t₁ ht₁ ht₁fin ϖ
  have hinf0 : ((infNatTrans ℤ χ₁.ker 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
      ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants χ₁.ker)).hom ⟨carryFun t₁ ht₁ ht₁fin (inclInv q M H hcompat K hK χ₁.ker ϖ), hc₁⟩) = 0 := by
    rw [inf_H2π_carryFun_eq χ₁.ker t₁ ht₁ ht₁fin hN₁ (inclInv q M H hcompat K hK χ₁.ker ϖ) hc₁
      (chiCocycle_mem_cocycles₂ _ _ (ρ_ofMul_incl q M H hcompat K hK ϖ))]
    refine Eq.trans ?_ hF1
    exact H2π_chiCocycle_congr hχ₁.symm _ _ _

  obtain ⟨hH1, -, -⟩ := ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
    q M H hH hcompat (isSolvable_H H) K hK u hu
  have hinj := (groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 (Rep.ofMulDistribMulAction H (↥M)ˣ) χ₁.ker (hH1 χ₁.ker)).1
  rw [infNatTrans_app] at hinf0
  have h0 : (H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants χ₁.ker)).hom ⟨carryFun t₁ ht₁ ht₁fin (inclInv q M H hcompat K hK χ₁.ker ϖ), hc₁⟩ = 0 :=
    hinj (hinf0.trans (map_zero _).symm)

  obtain ⟨b, hb, hprod⟩ := exists_norm_of_carry_eq_zero χ₁.ker t₁ ht₁ ht₁fin (incl q M H K hK ϖ)
    (fun h => smul_incl q M H hcompat K hK h ϖ) (ofMul_incl_mem q M H hcompat K hK χ₁.ker ϖ) hc₁ h0
  have hmem : σ ∈ χ₁.ker := h2 χ₁.ker ϖ ⟨b, hb, hprod⟩
  rw [MonoidHom.mem_ker] at hmem
  have hχσ : χ σ = (χ₀ ^ i) σ := by rw [hχeq, MonoidHom.mul_apply, hmem, one_mul]
  rw [hFeq, hEF0, show chiVal χ σ = chiVal (χ₀ ^ i) σ by rw [chiVal, chiVal, hχσ], hval0]

end Key2

end ExtCitation.LocalLevel.Prop6
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation.LocalLevel.Prop6"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation.LocalLevel"
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.ExtCitation"

open ExtCitation.LocalLevel.Prop6 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)

    (Nn : Subgroup H) [Nn.Normal] (φ : H) (π : (↥M)ˣ)
    (hzp : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ))
    (hfrob : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (hπH : ∀ h : H, h • π = π) (hπ1 : ‖((π : M) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖)

    (hexp : ∀ h : H, h ^ Nn.index = 1)

    (f : (↥K)ˣ →* H)
    (h1 : ∀ (a : (↥K)ˣ) (k : ℤ), ‖((a : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖ ^ k →
      (QuotientGroup.mk (f a) : H ⧸ Nn) = (QuotientGroup.mk φ : H ⧸ Nn) ^ k)
    (h2 : ∀ (H' : Subgroup H) (a : (↥K)ˣ),
      (∃ b : (↥M)ˣ, (∀ h ∈ H', h • b = b) ∧
        ∏ᶠ c : H ⧸ H', (Quotient.out c) • b = Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) →
      f a ∈ H')

    (H' : Subgroup H) [H'.Normal] (t : H ⧸ H') (ht : ∀ c : H ⧸ H', c ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (a : (↥K)ˣ) (m : ℕ) (hm : (QuotientGroup.mk (f a) : H ⧸ H') = t ^ m)
    (hfix : (Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp H'.subtype))
    (hc : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')
        ⟨Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a), hfix⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')) :
    ((infNatTrans ℤ H' 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')).hom
          ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')
            ⟨Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a), hfix⟩, hc⟩) =
      (m * Nat.card H') • u := by
  classical

  have hπK : ((π : M) : PadicAlgCl q) ∈ K := (hK.mem_iff (π : M)).2 (fun h => by rw [← hcompat, hπH])
  have hπ0 : ((π : M) : PadicAlgCl q) ≠ 0 := fun h0 =>
    π.ne_zero (Subtype.ext h0)
  let πK : (↥K)ˣ := Units.mk0 ⟨((π : M) : PadicAlgCl q), hπK⟩ (fun h => hπ0 (congrArg Subtype.val h))
  have hπKnorm : ‖((πK : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖ := rfl

  set U : Set (↥K)ˣ := {ϖ | ‖((ϖ : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖} with hU
  have hπmaxK : ∀ y : K, ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((πK : K) : PadicAlgCl q)‖ := by
    intro y hy
    rw [hπKnorm]
    exact hπmax ⟨(y : PadicAlgCl q), hK.le y.2⟩
      (fun h _ => (hK.mem_iff ⟨(y : PadicAlgCl q), hK.le y.2⟩).1 y.2 h) hy
  have hcoe : ∀ x : (↥K)ˣ, ((x : K) : PadicAlgCl q) = algebraMap K (PadicAlgCl q) (x : K) := fun x => rfl
  have hgen : ∀ b : (↥K)ˣ, b ∈ Subgroup.closure U := by
    intro b
    obtain ⟨k, hk⟩ := exists_norm_eq_norm_zpow q K πK (by rw [hπKnorm]; exact hπ1) hπmaxK b
    have hmemπ : πK ∈ Subgroup.closure U := Subgroup.subset_closure hπKnorm
    have hunif : b * πK ^ (1 - k) ∈ U := by
      change ‖(((b * πK ^ (1 - k) : (↥K)ˣ) : K) : PadicAlgCl q)‖ = _
      have e1 : (((b * πK ^ (1 - k) : (↥K)ˣ) : K) : PadicAlgCl q) =
          ((b : K) : PadicAlgCl q) * (((πK : K) : PadicAlgCl q)) ^ (1 - k) := by
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
        change algebraMap K (PadicAlgCl q) ((b : K) * (πK : K) ^ (1 - k)) = _
        rw [map_mul, map_zpow₀]
        rfl
      rw [e1, norm_mul, norm_zpow, hk, hπKnorm, ← zpow_add₀ (norm_ne_zero_iff.mpr hπ0), add_sub_cancel, zpow_one]
    have : b = (b * πK ^ (1 - k)) * πK ^ (k - 1) := by
      rw [mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hunif) (Subgroup.zpow_mem _ hmemπ _)

  have hall : ∀ χ, Fchi q M H hcompat K hK a χ = chiVal χ (f a) • u := fun χ =>
    Fchi_eq_of_generators q M H hcompat K hK (Echi q M H hH hcompat K hK u hu f) U
      (fun ϖ hϖ χ' => Fchi_uniformiser q M H hH hcompat K hK u hu Nn φ π hzp hfrob hπH hπ1 hπmax hexp f h1 h2 ϖ hϖ χ')
      a (hgen a) χ

  have htord : orderOf t = H'.index := orderOf_eq_index H t ht
  have hN' : orderOf t ∣ Nat.card H := by rw [htord]; exact H'.index_dvd_card
  rw [inf_H2π_carryFun_eq H' t ht htfin hN' ⟨_, hfix⟩ hc (chiCocycle_mem_cocycles₂ _ _ (ρ_ofMul_incl q M H hcompat K hK a))]
  change Fchi q M H hcompat K hK a (chiOf H' t ht htfin hN') = _
  rw [hall, chiVal, chiOf_apply_mk_eq H' t ht htfin hN' (f a) m hm, toAdd_ofAdd, ZMod.val_natCast,
    nsmul_mod_card q M H hH hcompat K hK u hu, htord, card_div_index H H', mul_comm]

end S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
end P2MW
export P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem (solution)
