-- Prove2me | solution 1 for FixedPoints.isDiscreteValuationRing_subring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/41fe87cc-f9ca-5b7f-9fa7-3573fe0dd9ac

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FixedPoints_isDiscreteValuationRing_subring

set_option autoImplicit false

open IsLocalRing IsDiscreteValuationRing

namespace HerbrandPortV

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Fintype H] [MulSemiringAction H R]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem prod_smul_mem_subring (x : R) : (∏ h : H, h • x) ∈ FixedPoints.subring R H := by
  intro g
  rw [Finset.smul_prod']
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem exists_mem_subring_addVal_pos :
    ∃ s ∈ FixedPoints.subring R H, s ≠ 0 ∧ 0 < addVal R s := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  refine ⟨∏ h : H, h • π, prod_smul_mem_subring π, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro h _ hzero
    exact hπ.ne_zero ((smul_eq_zero_iff_eq (α := H) h).mp hzero)
  · have h1 : addVal R π ≤ addVal R (∏ h : H, h • π) := by
      rw [addVal_le_iff_dvd]
      simpa using Finset.dvd_prod_of_mem (fun h : H => h • π) (Finset.mem_univ (1 : H))
    exact lt_of_lt_of_le (by rw [addVal_uniformizer hπ]; exact zero_lt_one) h1

end HerbrandPortV

namespace HerbrandPortV

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [MulSemiringAction H R]

omit [IsDiscreteValuationRing R] in

theorem mem_subring_of_mul_mem {t c : R} (ht : t ∈ FixedPoints.subring R H) (ht0 : t ≠ 0)
    (htc : t * c ∈ FixedPoints.subring R H) : c ∈ FixedPoints.subring R H := by
  intro h
  have h1 : t * (h • c) = t * c := by
    have := htc h
    rw [smul_mul', ht h] at this
    exact this
  exact mul_left_cancel₀ ht0 h1

theorem exists_addVal_eq_natCast {s : R} (hs : s ≠ 0) : ∃ n : ℕ, addVal R s = n := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (fun h => hs (addVal_eq_top_iff.mp h))
  exact ⟨n, hn.symm⟩

theorem isDiscreteValuationRing_subring [Finite H] :
    IsDiscreteValuationRing (FixedPoints.subring R H) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H

  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ s ∈ FixedPoints.subring R H, addVal R s = n
  have hP : ∃ n, P n := by
    obtain ⟨s, hs, hs0, hpos⟩ := exists_mem_subring_addVal_pos (R := R) (H := H)
    obtain ⟨n, hn⟩ := exists_addVal_eq_natCast hs0
    refine ⟨n, ?_, s, hs, hn⟩
    rw [hn] at hpos
    exact_mod_cast hpos
  obtain ⟨m, ⟨hm0, t, ht, htv⟩, hmin⟩ : ∃ m, P m ∧ ∀ n, P n → m ≤ n :=
    ⟨Nat.find hP, Nat.find_spec hP, fun n hn => Nat.find_min' hP hn⟩
  have ht0 : t ≠ 0 := fun h => by
    rw [h, addVal_zero] at htv
    exact ENat.top_ne_coe m htv

  have hge : ∀ s ∈ FixedPoints.subring R H, s ≠ 0 → ¬ IsUnit s → (m : ℕ∞) ≤ addVal R s := by
    intro s hs hs0 hsu
    obtain ⟨n, hn⟩ := exists_addVal_eq_natCast hs0
    rw [hn]
    have hn0 : 0 < n := by
      by_contra h0
      have : n = 0 := by omega
      subst this
      exact hsu (addVal_eq_zero_iff.mp (by exact_mod_cast hn))
    exact_mod_cast hmin n ⟨hn0, s, hs, hn⟩

  have key : ∀ s ∈ FixedPoints.subring R H, s ≠ 0 →
      ∃ q : ℕ, ∃ c ∈ FixedPoints.subring R H, IsUnit c ∧ s = t ^ q * c := by
    intro s hs hs0
    obtain ⟨v, hv⟩ := exists_addVal_eq_natCast hs0
    refine ⟨v / m, ?_⟩
    have hdvd : t ^ (v / m) ∣ s := by
      rw [← addVal_le_iff_dvd, addVal_pow, htv, hv, nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self v m
    obtain ⟨c, hc⟩ := hdvd
    have hcS : c ∈ FixedPoints.subring R H :=
      mem_subring_of_mul_mem ((FixedPoints.subring R H).pow_mem ht _) (pow_ne_zero _ ht0)
        (hc ▸ hs)
    have hc0 : c ≠ 0 := by rintro rfl; exact hs0 (by simpa using hc)
    refine ⟨c, hcS, ?_, hc⟩
    by_contra hcu
    have h1 := hge c hcS hc0 hcu
    obtain ⟨w, hw⟩ := exists_addVal_eq_natCast hc0
    have h2 : addVal R s = addVal R (t ^ (v / m)) + addVal R c := by rw [hc, addVal_mul]
    rw [addVal_pow, htv, hv, hw, nsmul_eq_mul] at h2
    rw [hw] at h1
    have h2' : v = (v / m) * m + w := by exact_mod_cast h2
    have h1' : m ≤ w := by exact_mod_cast h1
    have h3 := Nat.div_add_mod v m
    have hlt : v % m < m := Nat.mod_lt v hm0
    have h4 : (v / m) * m = m * (v / m) := mul_comm _ _
    omega

  let τ : FixedPoints.subring R H := ⟨t, ht⟩
  have hτu : ¬ IsUnit τ := fun h => by
    have h' : IsUnit t := (FixedPoints.isUnit_subring_iff τ).mp h
    have h1 : addVal R t = 0 := addVal_eq_zero_iff.mpr h'
    rw [htv] at h1
    exact hm0.ne' (by exact_mod_cast h1)
  have hτirr : Irreducible τ := by
    refine ⟨hτu, fun a b hab => ?_⟩
    by_contra hnot
    simp only [not_or] at hnot
    obtain ⟨hau, hbu⟩ := hnot
    have hab' : t = (a : R) * b := congrArg Subtype.val hab
    have ha0 : (a : R) ≠ 0 := fun h => ht0 (by rw [hab', h, zero_mul])
    have hb0 : (b : R) ≠ 0 := fun h => ht0 (by rw [hab', h, mul_zero])
    have ha := hge a a.2 ha0 (fun h => hau ((FixedPoints.isUnit_subring_iff a).mpr h))
    have hb := hge b b.2 hb0 (fun h => hbu ((FixedPoints.isUnit_subring_iff b).mpr h))
    have hsum : addVal R t = addVal R a + addVal R b := by rw [← addVal_mul, hab']
    rw [htv] at hsum
    have h1 : (m : ℕ∞) + m ≤ m := (add_le_add ha hb).trans hsum.symm.le
    have hmm : m + m ≤ m := by exact_mod_cast h1
    omega
  refine ofHasUnitMulPowIrreducibleFactorization ⟨τ, hτirr, ?_⟩
  intro x hx
  obtain ⟨q, c, hcS, hcu, hxc⟩ := key x x.2 (fun h => hx (Subtype.ext h))
  refine ⟨q, ?_⟩
  have hcu' : IsUnit (⟨c, hcS⟩ : FixedPoints.subring R H) :=
    (FixedPoints.isUnit_subring_iff _).mpr hcu
  exact ⟨hcu'.unit, Subtype.ext (by simp [τ, hxc])⟩

end HerbrandPortV

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] :
    IsDiscreteValuationRing (FixedPoints.subring R H) :=
  HerbrandPortV.isDiscreteValuationRing_subring

end S_FixedPoints_isDiscreteValuationRing_subring
end P2MW
export P2MW.S_FixedPoints_isDiscreteValuationRing_subring (solution)
