-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_index_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:19.603851+00:00
-- url     : https://prove2.me/submissions/40e92228-3af0-49ee-a42e-979df84e0c3b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Theorems.Thm_Formalism_HC_Der_Rd_KK_gcd
import Theorems.Thm_Formalism_HC_Der_Rd_card_KK
import Theorems.Thm_Formalism_HC_Der_Rd_half_le_rho
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_one_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_rho_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
private theorem card_le_natCard_subgroup_of_forall_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (s : Finset G) (hs : ∀ x ∈ s, x ∈ H) : s.card ≤ Nat.card H := by
  have h1 : (s : Set G) ⊆ (H : Set G) := fun x hx => hs x hx
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h2
  calc s.card ≤ (H : Set G).ncard := h2
    _ = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
private theorem eq_one_of_mem_KK_self {u : (ZMod N)ˣ}
    (hu : u ∈ KK N N) : u = 1 := by
  have h := mem_KK.mp hu
  have h' : ((u : ZMod N).val : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact h
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h'
  exact Units.ext h'
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Real.log U.index ≤ 2 * SS U := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hex : ∃ f, f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U :=
    ⟨N, dvd_rfl, fun u hu => by rw [eq_one_of_mem_KK_self hu]; exact U.one_mem⟩
  obtain ⟨c, hc, hcmin⟩ : ∃ c, (c ∣ N ∧ ∀ u ∈ KK N c, u ∈ U) ∧
      ∀ f, (f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U) → c ≤ f :=
    ⟨Nat.find hex, Nat.find_spec hex, fun f hf => Nat.find_min' hex hf⟩
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hc.1 (Nat.pos_of_ne_zero hN0)
  have hcdvd : ∀ f, f ∣ N → (∀ u ∈ KK N f, u ∈ U) → c ∣ f := by
    intro f hf hfU
    have hle : c ≤ Nat.gcd c f :=
      hcmin _ ⟨(Nat.gcd_dvd_left c f).trans hc.1, KK_gcd U hc.1 hf hc.2 hfU⟩
    have heq : Nat.gcd c f = c := le_antisymm (Nat.le_of_dvd hcpos (Nat.gcd_dvd_left c f)) hle
    rw [← heq]; exact Nat.gcd_dvd_right c f
  obtain ⟨k, hk⟩ := hc.1
  have hk0 : k ≠ 0 := by intro h0; apply hN0; rw [hk, h0, mul_zero]
  have hKpos : 0 < (KK N c).card :=
    Finset.card_pos.mpr ⟨1, one_mem_KK hc.1⟩
  have hKc := card_KK (N := N) hc.1
  have hKU : (KK N c).card ≤ Nat.card U :=
    card_le_natCard_subgroup_of_forall_mem U _ (fun u hu => hc.2 u hu)
  have hGU : Nat.card U * U.index = N.totient := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hidx : U.index ≤ c.totient := by
    have h1 : U.index * (KK N c).card ≤ c.totient * (KK N c).card := by
      calc U.index * (KK N c).card ≤ U.index * Nat.card U := Nat.mul_le_mul_left _ hKU
        _ = N.totient := by rw [mul_comm, hGU]
        _ = c.totient * (KK N c).card := by rw [← hKc, mul_comm]
    exact Nat.le_of_mul_le_mul_right h1 hKpos
  have hidx0 : 0 < U.index := Nat.pos_of_ne_zero (fun h => by
    rw [h, mul_zero] at hGU
    exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne' hGU.symm)
  have hlog1 : Real.log U.index ≤ Real.log c := by
    apply Real.log_le_log (by exact_mod_cast hidx0)
    exact_mod_cast hidx.trans (Nat.totient_le c)
  have hfilt : N.divisors.filter (fun m => c ∣ N / m) = k.divisors := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hm, -⟩, hcm⟩
      refine ⟨?_, hk0⟩
      obtain ⟨j, hj⟩ := hcm
      have h1 : N = m * (c * j) := by rw [← hj, Nat.mul_div_cancel' hm]
      have h2 : c * k = c * (m * j) := by rw [← hk, h1]; ring
      exact ⟨j, Nat.eq_of_mul_eq_mul_left hcpos h2⟩
    · rintro ⟨⟨j, hj⟩, -⟩
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos ⟨j, hj⟩ (Nat.pos_of_ne_zero hk0)
      refine ⟨⟨?_, hN0⟩, ?_⟩
      · rw [hk, hj]; exact ⟨c * j, by ring⟩
      · have h1 : N / m = c * j := by
          rw [hk, hj, show c * (m * j) = m * (c * j) by ring, Nat.mul_div_cancel_left _ hm0]
        rw [h1]; exact dvd_mul_right c j
  have hsplit : Real.log k + ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m
      = Real.log N := by
    rw [← vonMangoldt_sum (n := k), ← hfilt, Finset.sum_filter_add_sum_filter_not, vonMangoldt_sum]
  have hlogN : Real.log (N : ℝ) = Real.log c + Real.log k := by
    rw [hk, Nat.cast_mul, Real.log_mul (by exact_mod_cast hcpos.ne') (by exact_mod_cast hk0)]
  have hbound : ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m
      ≤ ∑ m ∈ N.divisors, 2 * (vonMangoldt m * rho U (N / m)) := by
    calc _ ≤ ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m),
          2 * (vonMangoldt m * rho U (N / m)) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_filter, Nat.mem_divisors] at hm
          have hmN : N / m ∣ N := Nat.div_dvd_of_dvd hm.1.1
          have hex' : ∃ u ∈ KK N (N / m), u ∉ U := by
            by_contra hcon
            push_neg at hcon
            exact hm.2 (hcdvd _ hmN hcon)
          have h12 := half_le_rho U hmN hex'
          have hΛ : 0 ≤ vonMangoldt m := vonMangoldt_nonneg
          nlinarith
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m _ _
          exact mul_nonneg zero_le_two
            (mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))
  unfold SS
  rw [Finset.mul_sum]
  linarith
end Formalism.HC.Der.Rd
