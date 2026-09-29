-- Prove2me | solution 1 for FormalGroup.coeff_one_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/054936ed-e124-5ffb-912d-f57f918ef507

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_coeff_one_nthSeries

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup
p2m_export "FormalGroup" "zero_constantCoeff lin_coeff_Y lin_coeff_X toPowerSeries nthSeries nthSeries_succ constantCoeff_nthSeries hasSubst_nthSeries"
p2m_open "FormalGroup"

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

section LinearCoefficient

private theorem fin_two_finsupp_cases (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 ≤ 1) :
    d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
  have hext : ∀ e : Fin 2 →₀ ℕ, d 0 = e 0 → d 1 = e 1 → d = e := fun e h0 h1 =>
    Finsupp.ext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
  · rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · refine Or.inl (hext 0 ?_ ?_)
      · simpa using h0
      · simpa using h1
    · have h1' : d 1 = 1 := le_antisymm (by omega) h1
      refine Or.inr (Or.inr (hext _ ?_ ?_))
      · rw [Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        exact h0
      · rw [Finsupp.single_eq_same]
        exact h1'
  · have h0' : d 0 = 1 := le_antisymm (by omega) h0
    have h1 : d 1 = 0 := by omega
    refine Or.inr (Or.inl (hext _ ?_ ?_))
    · rw [Finsupp.single_eq_same]
      exact h0'
    · rw [Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      exact h1

theorem coeff_one_nthSeries_s18 (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.nthSeries n) = (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    classical

    set a : Fin 2 → PowerSeries R := ![F.nthSeries n, PowerSeries.X] with ha_def
    have ha : MvPowerSeries.HasSubst a := F.hasSubst_nthSeries n

    have hXdvd : (PowerSeries.X : PowerSeries R) ∣ F.nthSeries n :=
      PowerSeries.X_dvd_iff.mpr (F.constantCoeff_nthSeries n)

    have hcoeff_eq : (PowerSeries.coeff (R := R) 1)
        = MvPowerSeries.coeff (Finsupp.single () 1) :=
      PowerSeries.coeff_def Finsupp.single_eq_same
    rw [nthSeries_succ, ← ha_def, hcoeff_eq, MvPowerSeries.coeff_subst ha]

    set g : (Fin 2 →₀ ℕ) → R := fun d =>
      MvPowerSeries.coeff d F.toPowerSeries •
        MvPowerSeries.coeff (Finsupp.single () 1) (d.prod fun s i => (a s) ^ i) with hg_def

    have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s i => (a s) ^ i)
        = (F.nthSeries n) ^ (d 0) * (PowerSeries.X : PowerSeries R) ^ (d 1) := by
      intro d
      rw [Finsupp.prod_pow, Fin.prod_univ_two]
      simp [a]
    have hzero_of_two_le : ∀ d : Fin 2 →₀ ℕ, 2 ≤ d 0 + d 1 →
        MvPowerSeries.coeff (Finsupp.single () 1) (d.prod fun s i => (a s) ^ i) = 0 := by
      intro d hd2
      have hdvd : (PowerSeries.X : PowerSeries R) ^ 2 ∣ (d.prod fun s i => (a s) ^ i) := by
        rw [hprod d]
        calc (PowerSeries.X : PowerSeries R) ^ 2
            ∣ (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) := pow_dvd_pow _ hd2
          _ = (PowerSeries.X : PowerSeries R) ^ (d 0)
              * (PowerSeries.X : PowerSeries R) ^ (d 1) := pow_add _ _ _
          _ ∣ (F.nthSeries n) ^ (d 0) * (PowerSeries.X : PowerSeries R) ^ (d 1) :=
              mul_dvd_mul (pow_dvd_pow_of_dvd hXdvd _) dvd_rfl
      have h1 : PowerSeries.coeff 1 (d.prod fun s i => (a s) ^ i) = 0 :=
        PowerSeries.X_pow_dvd_iff.mp hdvd 1 one_lt_two
      rw [hcoeff_eq] at h1
      exact h1

    have hsupp : Function.support g ⊆
        ({0, Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
      intro d hd
      by_contra hd_not
      apply hd
      rcases Nat.lt_or_ge (d 0 + d 1) 2 with hlt | hge
      ·
        rcases fin_two_finsupp_cases d (by omega) with rfl | rfl | rfl <;> simp_all
      ·
        rw [hg_def]
        simp only [hzero_of_two_le d hge, smul_zero]

    rw [finsum_eq_finsetSum_of_support_subset g hsupp]

    have hne01 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
      intro h
      have := DFunLike.congr_fun h 0
      simp at this
    have hne02 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
      intro h
      have := DFunLike.congr_fun h 1
      simp at this
    have hne12 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
      intro h
      have := DFunLike.congr_fun h 0
      simp at this

    rw [Finset.sum_insert (by simp [hne01, hne02]),
      Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]

    have hterm0 : g 0 = 0 := by
      rw [hg_def]
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.zero_constantCoeff,
        zero_smul]

    have hterm1 : g (Finsupp.single 0 1) = (n : R) := by
      rw [hg_def]
      simp only []
      rw [F.lin_coeff_X, Finsupp.prod_single_index (by rw [pow_zero]), pow_one]
      have ha0 : a 0 = F.nthSeries n := by simp [a]
      rw [ha0, one_smul, ← hcoeff_eq, ih]

    have hterm2 : g (Finsupp.single 1 1) = 1 := by
      rw [hg_def]
      simp only []
      rw [F.lin_coeff_Y, Finsupp.prod_single_index (by rw [pow_zero]), pow_one]
      have ha1 : a 1 = PowerSeries.X := by simp [a]
      rw [ha1, one_smul, ← hcoeff_eq, PowerSeries.coeff_one_X]
    rw [hterm0, hterm1, hterm2]
    push_cast
    ring

end LinearCoefficient

end FormalGroup

end

end

end

theorem solution {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.nthSeries n) = (n : R) :=
  FormalGroup.coeff_one_nthSeries_s18 F n

end S_FormalGroup_coeff_one_nthSeries
end P2MW
export P2MW.S_FormalGroup_coeff_one_nthSeries (solution)
