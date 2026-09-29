-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/aa454ca4-8674-54bc-aa45-3dfff0eabead

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_natCard_H2_units_eq_natCard_of_isCyclic
import Theorems.Thm_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology P2MW.S_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun.groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun.ExtCitation.LocalLevel"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2 H2π congr cocycles₂ d₁₂_hom_apply coboundaries₂_le_cocycles₂ coboundaries₂ map cocycles functor π H2π_eq_iff cyclicLog carryFun cyclicInv carryFun_mem_cocycles2"
p2m_open "groupCohomology"
namespace Ws25C2
variable {G : Type} [Group G]

theorem pow_cyclicLog (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : G) :
    s ^ cyclicLog s hs hfin g = g := by
  unfold cyclicLog
  have := (finEquivZPowers hfin).apply_symm_apply ⟨g, hs g⟩
  rw [finEquivZPowers_apply] at this
  exact congrArg Subtype.val this

theorem cyclicLog_lt (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : G) :
    cyclicLog s hs hfin g < orderOf s :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩).isLt

theorem cyclicLog_eq_of_pow_eq (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {i : ℕ} (hi : i < orderOf s) {g : G} (h : s ^ i = g) : cyclicLog s hs hfin g = i := by
  apply pow_injOn_Iio_orderOf (x := s)
  · exact cyclicLog_lt s hs hfin g
  · exact hi
  · show s ^ cyclicLog s hs hfin g = s ^ i
    rw [pow_cyclicLog, h]

theorem cyclicLog_pow (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (m : ℕ) :
    cyclicLog s hs hfin (s ^ m) = m % orderOf s :=
  cyclicLog_eq_of_pow_eq s hs hfin (Nat.mod_lt _ (orderOf_pos_iff.mpr hfin)) (pow_mod_orderOf s m)

theorem carryFun_apply (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) (g h : G) :
    carryFun s hs hfin a (g, h) = if orderOf s ≤ cyclicLog s hs hfin g + cyclicLog s hs hfin h then a else 0 := rfl

theorem sum_range_orderOf_shift (s : G) {A : Rep ℤ G} (γ : G → A) :
    (∑ i ∈ Finset.range (orderOf s), γ (s ^ (i + 1))) = ∑ i ∈ Finset.range (orderOf s), γ (s ^ i) := by
  have := Finset.sum_range_succ' (fun k => γ (s ^ k)) (orderOf s)
  rw [Finset.sum_range_succ, pow_orderOf_eq_one, pow_zero] at this
  exact (add_right_cancel this).symm

theorem cyclicInv_dOne (s : G) {A : Rep ℤ G} (β : G → A) :
    cyclicInv s ((d₁₂ A).hom β) = ∑ i ∈ Finset.range (orderOf s), A.ρ (s ^ i) (β s) := by
  unfold cyclicInv
  simp only [d₁₂_hom_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ i ∈ Finset.range (orderOf s), β (s ^ i * s)) = ∑ i ∈ Finset.range (orderOf s), β (s ^ i) := by
    simp_rw [← pow_succ]
    exact sum_range_orderOf_shift s β
  rw [h1]
  abel

theorem cyclicInv_carryFun (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) (hn : orderOf s ≠ 1) :
    cyclicInv s (carryFun s hs hfin a) = a := by
  have hpos : 0 < orderOf s := orderOf_pos_iff.mpr hfin
  have h2 : 2 ≤ orderOf s := by omega
  have hlog1 : cyclicLog s hs hfin s = 1 := cyclicLog_eq_of_pow_eq s hs hfin (i := 1) (by omega) (pow_one s)
  unfold cyclicInv
  rw [Finset.sum_eq_single (orderOf s - 1)]
  · rw [carryFun_apply, cyclicLog_pow, hlog1, Nat.mod_eq_of_lt (by omega : orderOf s - 1 < orderOf s)]
    rw [if_pos (by omega)]
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rw [carryFun_apply, cyclicLog_pow, hlog1, Nat.mod_eq_of_lt hi]
    rw [if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem cyclicInv_add (s : G) {A : Rep ℤ G} (c c' : G × G → A) :
    cyclicInv s (c + c') = cyclicInv s c + cyclicInv s c' := by
  unfold cyclicInv
  simp only [Pi.add_apply, Finset.sum_add_distrib]

theorem cyclicInv_zero (s : G) {A : Rep ℤ G} : cyclicInv s (0 : G × G → A) = 0 := by
  unfold cyclicInv
  simp only [Pi.zero_apply, Finset.sum_const_zero]

theorem natCard_eq_orderOf (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) : Nat.card G = orderOf s := by
  rw [← Nat.card_zpowers s, (Subgroup.eq_top_iff' _).mpr hs, Subgroup.card_top]

theorem exists_addMonoidHom_H2 {A : Rep ℤ G} {M : Type} [AddCommGroup M] (Φ : cocycles₂ A →+ M)
    (hΦ : ∀ β : G → A, ∀ hβ : (d₁₂ A).hom β ∈ cocycles₂ A, Φ ⟨(d₁₂ A).hom β, hβ⟩ = 0) :
    ∃ Ψ : groupCohomology.H2 A →+ M, ∀ c : cocycles₂ A, Ψ ((H2π A).hom c) = Φ c := by
  have hsurj : Function.Surjective (H2π A).hom :=
    (ModuleCat.epi_iff_surjective (H2π A)).mp inferInstance

  have hker : ∀ c c' : cocycles₂ A, (H2π A).hom c = (H2π A).hom c' → Φ c = Φ c' := by
    intro c c' h
    have h' : (⇑c : G × G → A) - ⇑c' ∈ coboundaries₂ A := (H2π_eq_iff c c').mp h
    obtain ⟨β, hβ⟩ := h'
    have hmem : (d₁₂ A).hom β ∈ cocycles₂ A := coboundaries₂_le_cocycles₂ A ⟨β, rfl⟩
    have hsub : c - c' = ⟨(d₁₂ A).hom β, hmem⟩ := by
      apply Subtype.ext
      show (⇑c : G × G → A) - ⇑c' = (d₁₂ A).hom β
      exact hβ.symm
    have := hΦ β hmem
    rw [← hsub, map_sub, sub_eq_zero] at this
    exact this
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : groupCohomology.H2 A →+ M, ∀ x, Ψ x = Φ (Function.surjInv hsurj x) :=
    ⟨{ toFun := fun x => Φ (Function.surjInv hsurj x)
       map_zero' := by
         show Φ (Function.surjInv hsurj 0) = 0
         rw [hker _ 0 (by rw [Function.surjInv_eq hsurj, map_zero]), map_zero]
       map_add' := fun x y => by
         show Φ (Function.surjInv hsurj (x + y)) = Φ (Function.surjInv hsurj x) + Φ (Function.surjInv hsurj y)
         rw [← map_add]
         apply hker
         rw [map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj] },
     fun _ => rfl⟩
  refine ⟨Ψ, fun c => ?_⟩
  rw [hΨ]
  apply hker
  rw [Function.surjInv_eq hsurj]

theorem exists_addEquiv_of_valuation (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (v : A →+ ℤ) (hv : ∀ (g : G) (x : A), v (A.ρ g x) = v x)
    (hcard : Nat.card (groupCohomology.H2 A) = Nat.card G)
    (π : A) (hπc : carryFun s hs hfin π ∈ cocycles₂ A) (hvπ : v π = 1) :
    ∃ inv : groupCohomology.H2 A ≃+ ZMod (Nat.card G), ∀ (a : A) (hc : carryFun s hs hfin a ∈ cocycles₂ A),
      inv ((H2π A).hom ⟨carryFun s hs hfin a, hc⟩) = ((v a : ℤ) : ZMod (Nat.card G)) := by
  have hn : Nat.card G = orderOf s := natCard_eq_orderOf s hs
  have hpos : 0 < orderOf s := orderOf_pos_iff.mpr hfin
  haveI : NeZero (Nat.card G) := ⟨by rw [hn]; exact hpos.ne'⟩

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : cocycles₂ A →+ ZMod (Nat.card G),
      ∀ c : cocycles₂ A, Φ c = ((v (cyclicInv s ⇑c) : ℤ) : ZMod (Nat.card G)) :=
    ⟨{ toFun := fun c => ((v (cyclicInv s ⇑c) : ℤ) : ZMod (Nat.card G))
       map_zero' := by
         show ((v (cyclicInv s (0 : G × G → A)) : ℤ) : ZMod (Nat.card G)) = 0
         rw [cyclicInv_zero, map_zero, Int.cast_zero]
       map_add' := fun c c' => by
         show ((v (cyclicInv s ((c : G × G → A) + (c' : G × G → A))) : ℤ) : ZMod (Nat.card G)) =
           ((v (cyclicInv s ⇑c) : ℤ) : ZMod (Nat.card G)) + ((v (cyclicInv s ⇑c') : ℤ) : ZMod (Nat.card G))
         rw [cyclicInv_add, map_add, Int.cast_add] },
     fun _ => rfl⟩

  have hΦ0 : ∀ β : G → A, ∀ hβ : (d₁₂ A).hom β ∈ cocycles₂ A, Φ ⟨(d₁₂ A).hom β, hβ⟩ = 0 := by
    intro β hβ
    rw [hΦ]
    show ((v (cyclicInv s ((d₁₂ A).hom β)) : ℤ) : ZMod (Nat.card G)) = 0
    rw [cyclicInv_dOne, map_sum]
    simp_rw [hv]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ← hn,
      ZMod.natCast_self, zero_mul]
  obtain ⟨Ψ, hΨ⟩ := exists_addMonoidHom_H2 Φ hΦ0

  have hval : ∀ (a : A) (hc : carryFun s hs hfin a ∈ cocycles₂ A),
      Ψ ((H2π A).hom ⟨carryFun s hs hfin a, hc⟩) = ((v a : ℤ) : ZMod (Nat.card G)) := by
    intro a hc
    rw [hΨ, hΦ]
    by_cases h1 : orderOf s = 1
    · haveI : Subsingleton (ZMod (Nat.card G)) := ZMod.subsingleton_iff.mpr (hn.trans h1)
      exact Subsingleton.elim _ _
    · show ((v (cyclicInv s (carryFun s hs hfin a)) : ℤ) : ZMod (Nat.card G)) = _
      rw [cyclicInv_carryFun s hs hfin a h1]

  have hsurj : Function.Surjective Ψ := by
    intro y
    refine ⟨y.val • (H2π A).hom ⟨carryFun s hs hfin π, hπc⟩, ?_⟩
    rw [map_nsmul, hval, hvπ, Int.cast_one, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

  haveI : Finite (groupCohomology.H2 A) :=
    Nat.finite_of_card_ne_zero (by rw [hcard, hn]; exact hpos.ne')
  have hbij : Function.Bijective Ψ :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  exact ⟨AddEquiv.ofBijective Ψ hbij, fun a hc => by rw [AddEquiv.ofBijective_apply]; exact hval a hc⟩

end Ws25C2
end groupCohomology

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic LocalLevel.exists_fixedLevel_quotientToInvariants_iso"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "natCard_H2_units_eq_natCard_of_isCyclic exists_fixedLevel_quotientToInvariants_iso"
namespace Ws25C2N
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable (q : ℕ) [Fact q.Prime]
variable (L : IntermediateField ℚ_[q] (PadicAlgCl q))
variable (G : Type) [Group G] [MulSemiringAction G L]

noncomputable def autOf (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) :
    L ≃ₐ[ℚ_[q]] L :=
  { MulSemiringAction.toRingEquiv G L g with
    commutes' := fun x => hG g x }

theorem autOf_apply (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x : L) :
    autOf q L G hG g x = g • x := rfl

theorem norm_smul_eq (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x : L) :
    ‖((g • x : L) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ := by
  haveI : Normal ℚ_[q] (PadicAlgCl q) := IsAlgClosure.normal ℚ_[q] (PadicAlgCl q)
  have hcomm : (autOf q L G hG g).liftNormal (PadicAlgCl q) (algebraMap L (PadicAlgCl q) x) =
      algebraMap L (PadicAlgCl q) (autOf q L G hG g x) :=
    AlgEquiv.liftNormal_commutes (autOf q L G hG g) (PadicAlgCl q) x
  have h1 : ((g • x : L) : PadicAlgCl q) = (autOf q L G hG g).liftNormal (PadicAlgCl q) (x : PadicAlgCl q) := by
    rw [← autOf_apply q L G hG g x]
    exact hcomm.symm
  rw [h1]
  have := nnnorm_padicAlgCl_algEquiv q ((autOf q L G hG g).liftNormal (PadicAlgCl q)) (x : PadicAlgCl q)
  have := congrArg NNReal.toReal this
  simpa only [coe_nnnorm] using this

variable {q L}

theorem norm_pos_of_unit (u : (↥L)ˣ) : 0 < ‖((u : L) : PadicAlgCl q)‖ := by
  rw [norm_pos_iff]
  intro h
  apply u.ne_zero
  exact_mod_cast h

theorem norm_unit_mul (u w : (↥L)ˣ) :
    ‖(((u * w : (↥L)ˣ) : L) : PadicAlgCl q)‖ = ‖((u : L) : PadicAlgCl q)‖ * ‖((w : L) : PadicAlgCl q)‖ := by
  rw [Units.val_mul]
  push_cast
  exact norm_mul _ _

theorem norm_unit_zpow (u : (↥L)ˣ) (m : ℤ) :
    ‖(((u ^ m : (↥L)ˣ) : L) : PadicAlgCl q)‖ = ‖((u : L) : PadicAlgCl q)‖ ^ m := by
  rw [Units.val_zpow_eq_zpow_val]
  have : (((u : L) ^ m : L) : PadicAlgCl q) = ((u : L) : PadicAlgCl q) ^ m :=
    map_zpow₀ (algebraMap L (PadicAlgCl q)) (u : L) m
  rw [this, norm_zpow]

variable {G}
variable [MulDistribMulAction G (↥L)ˣ]

theorem smul_coe_eq_of_smul_eq (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    {g : G} {u : (↥L)ˣ} (h : g • u = u) : g • (u : L) = u := by
  rw [← hcompat, h]

theorem smul_eq_of_smul_coe_eq (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    {g : G} {u : (↥L)ˣ} (h : g • (u : L) = u) : g • u = u := by
  apply Units.ext
  rw [hcompat, h]

theorem exists_norm_eq_zpow_of_fixed (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G) (π : (↥L)ˣ) (hπN : ∀ n ∈ N, n • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (u : (↥L)ˣ) (hu : ∀ n ∈ N, n • u = u) :
    ∃ i : ℤ, ‖((u : L) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ i := by
  set r := ‖((π : L) : PadicAlgCl q)‖ with hr
  have hr0 : 0 < r := norm_pos_of_unit π
  have hu0 : 0 < ‖((u : L) : PadicAlgCl q)‖ := norm_pos_of_unit u
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hu0 (one_lt_inv₀ hr0 |>.mpr hπ1)
  rw [inv_zpow'] at hm1
  rw [inv_zpow', neg_add] at hm2

  have hz : ‖(((u * π ^ (m + 1) : (↥L)ˣ) : L) : PadicAlgCl q)‖ = ‖((u : L) : PadicAlgCl q)‖ * r ^ (m + 1) := by
    rw [norm_unit_mul, norm_unit_zpow]
  have hzN : ∀ n ∈ N, n • (((u * π ^ (m + 1) : (↥L)ˣ) : L)) = ((u * π ^ (m + 1) : (↥L)ˣ) : L) := by
    intro n hn
    apply smul_coe_eq_of_smul_eq hcompat
    rw [smul_mul', smul_zpow', hu n hn, hπN n hn]
  have hz1 : ‖(((u * π ^ (m + 1) : (↥L)ˣ) : L) : PadicAlgCl q)‖ < 1 := by
    rw [hz]
    calc ‖((u : L) : PadicAlgCl q)‖ * r ^ (m + 1) < r ^ (-m + -1) * r ^ (m + 1) :=
          mul_lt_mul_of_pos_right hm2 (zpow_pos hr0 _)
      _ = 1 := by rw [← zpow_add₀ hr0.ne', show -m + -1 + (m + 1) = 0 by ring, zpow_zero]
  have hzr : r ≤ ‖(((u * π ^ (m + 1) : (↥L)ˣ) : L) : PadicAlgCl q)‖ := by
    rw [hz]
    calc r = r ^ (-m) * r ^ (m + 1) := by rw [← zpow_add₀ hr0.ne', show -m + (m + 1) = 1 by ring, zpow_one]
      _ ≤ ‖((u : L) : PadicAlgCl q)‖ * r ^ (m + 1) := mul_le_mul_of_nonneg_right hm1 (zpow_pos hr0 _).le
  have hzeq : ‖(((u * π ^ (m + 1) : (↥L)ˣ) : L) : PadicAlgCl q)‖ = r := le_antisymm (hπmax _ hzN hz1) hzr
  refine ⟨-m, ?_⟩
  rw [hz] at hzeq

  have : ‖((u : L) : PadicAlgCl q)‖ = r * (r ^ (m + 1))⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ (zpow_pos hr0 _).ne').mpr hzeq
  rw [this, ← zpow_neg, ← zpow_one_add₀ hr0.ne']
  congr 1
  ring

section ord
variable (N : Subgroup G) (π : (↥L)ˣ) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
variable (hex : ∀ u : (↥L)ˣ, (∀ n ∈ N, n • u = u) → ∃ i : ℤ, ‖((u : L) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ i)

open Classical in

noncomputable def ord (u : (↥L)ˣ) : ℤ :=
  if h : ∀ n ∈ N, n • u = u then Classical.choose (hex u h) else 0

omit [MulSemiringAction G L] in
theorem norm_eq_zpow_ord {u : (↥L)ˣ} (hu : ∀ n ∈ N, n • u = u) :
    ‖((u : L) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ ord N π hex u := by
  unfold ord
  rw [dif_pos hu]
  exact Classical.choose_spec (hex u hu)

include hπ1 in
theorem zpow_norm_injective : Function.Injective fun n : ℤ => ‖((π : L) : PadicAlgCl q)‖ ^ n :=
  (zpow_right_strictAnti₀ (norm_pos_of_unit π) hπ1).injective

omit [MulSemiringAction G L] in
include hπ1 in
theorem ord_eq_of_norm_eq {u : (↥L)ˣ} (hu : ∀ n ∈ N, n • u = u) {k : ℤ}
    (h : ‖((u : L) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k) : ord N π hex u = k :=
  zpow_norm_injective π hπ1 ((norm_eq_zpow_ord N π hex hu).symm.trans h)

omit [MulSemiringAction G L] in
theorem fixed_mul {u w : (↥L)ˣ} (hu : ∀ n ∈ N, n • u = u) (hw : ∀ n ∈ N, n • w = w) :
    ∀ n ∈ N, n • (u * w) = u * w := fun n hn => by
  rw [smul_mul', hu n hn, hw n hn]

omit [MulSemiringAction G L] in
include hπ1 in
theorem ord_mul {u w : (↥L)ˣ} (hu : ∀ n ∈ N, n • u = u) (hw : ∀ n ∈ N, n • w = w) :
    ord N π hex (u * w) = ord N π hex u + ord N π hex w := by
  apply ord_eq_of_norm_eq N π hπ1 hex (fixed_mul N hu hw)
  rw [norm_unit_mul, norm_eq_zpow_ord N π hex hu, norm_eq_zpow_ord N π hex hw, ← zpow_add₀ (norm_pos_of_unit π).ne']

omit [MulSemiringAction G L] in
include hπ1 in
theorem ord_one : ord N π hex 1 = 0 :=
  ord_eq_of_norm_eq N π hπ1 hex (fun n _ => smul_one n) (by rw [zpow_zero, Units.val_one]; push_cast; exact norm_one)

variable [N.Normal]

omit [MulSemiringAction G L] in

theorem fixed_of_mem (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) :
    ∀ n ∈ N, n • (Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) = Additive.toMul (a.1 : Additive (↥L)ˣ) :=
  fun n hn => congrArg Additive.toMul (a.2 ⟨n, hn⟩)

noncomputable def ordHom : ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) →+ ℤ :=
  { toFun := fun a => ord N π hex (Additive.toMul (a.1 : Additive (↥L)ˣ))
    map_zero' := by
      show ord N π hex (Additive.toMul (0 : Additive (↥L)ˣ)) = 0
      rw [toMul_zero, ord_one N π hπ1 hex]
    map_add' := fun a b => by
      show ord N π hex ((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) * (Additive.toMul (b.1 : Additive (↥L)ˣ) : (↥L)ˣ)) =
        ord N π hex (Additive.toMul (a.1 : Additive (↥L)ˣ)) + ord N π hex (Additive.toMul (b.1 : Additive (↥L)ˣ))
      rw [ord_mul N π hπ1 hex (fixed_of_mem N a) (fixed_of_mem N b)] }

omit [MulSemiringAction G L] in
theorem ordHom_apply (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) :
    ordHom N π hπ1 hex a = ord N π hex (Additive.toMul (a.1 : Additive (↥L)ˣ)) := rfl

end ord

end ExtCitation.LocalLevel.Ws25C2N

open groupCohomology.Ws25C2 ExtCitation.LocalLevel.Ws25C2N in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    ∃ inv : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ≃+ ZMod (Nat.card (G ⧸ N)),
      ∀ (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k →
          inv ((H2π ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)).hom
              ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hc⟩) = (k : ZMod (Nat.card (G ⧸ N))) := by

  have hex : ∀ u : (↥L)ˣ, (∀ n ∈ N, n • u = u) →
      ∃ i : ℤ, ‖((u : L) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ i :=
    exists_norm_eq_zpow_of_fixed hcompat N π (fun n _ => hπG n) hπ1 hπmax

  have hcard : Nat.card (groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)) =
      Nat.card (G ⧸ N) := by
    obtain ⟨L', i1, i2, i3, i4, hG', hcompat', ⟨e⟩⟩ :=
      ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso q L G hG hcompat N
    haveI : IsCyclic (G ⧸ N) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr ⟨QuotientGroup.mk' N φ, (Subgroup.eq_top_iff' _).mpr hφN⟩
    rw [← ExtCitation.LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic q L' (G ⧸ N) hG' hcompat']
    exact Nat.card_congr ((groupCohomology.functor ℤ (G ⧸ N) 2).mapIso e).toLinearEquiv.toEquiv

  have hv : ∀ (g : G ⧸ N) (x : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N),
      ordHom N π hπ1 hex (((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N).ρ g x) = ordHom N π hπ1 hex x := by
    intro g x
    induction g using QuotientGroup.induction_on with
    | H g =>
      rw [ordHom_apply, ordHom_apply]
      apply ord_eq_of_norm_eq N π hπ1 hex (fixed_of_mem N _)
      have hgx : (Additive.toMul ((((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N).ρ
          (QuotientGroup.mk g) x).1 : Additive (↥L)ˣ) : (↥L)ˣ) = g • (Additive.toMul (x.1 : Additive (↥L)ˣ) : (↥L)ˣ) := rfl
      rw [hgx, hcompat, norm_smul_eq q L G hG]
      exact norm_eq_zpow_ord N π hex (fixed_of_mem N x)

  have hπN : ∀ n : ↥N, ((Rep.ofMulDistribMulAction G (↥L)ˣ).ρ.comp N.subtype) n (Additive.ofMul π : Additive (↥L)ˣ) =
      Additive.ofMul π :=
    fun n => by
      show Additive.ofMul ((n : G) • π) = Additive.ofMul π
      rw [hπG]
  have hπc : carryFun (QuotientGroup.mk' N φ) hφN hfinN
      (⟨Additive.ofMul π, hπN⟩ : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ∈
      cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) := by
    apply groupCohomology.carryFun_mem_cocycles2
    apply Subtype.ext
    show Additive.ofMul (φ • π) = Additive.ofMul π
    rw [hπG]
  have hvπ : ordHom N π hπ1 hex (⟨Additive.ofMul π, hπN⟩ : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) = 1 := by
    show ord N π hex π = 1
    exact ord_eq_of_norm_eq N π hπ1 hex (fun n _ => hπG n) (by rw [zpow_one])
  obtain ⟨inv, hinv⟩ := exists_addEquiv_of_valuation (QuotientGroup.mk' N φ) hφN hfinN (ordHom N π hπ1 hex) hv hcard _ hπc hvπ
  refine ⟨inv, fun a k hc hak => ?_⟩
  rw [hinv, ordHom_apply, ord_eq_of_norm_eq N π hπ1 hex (fixed_of_mem N a) hak]

end S_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun (solution)
