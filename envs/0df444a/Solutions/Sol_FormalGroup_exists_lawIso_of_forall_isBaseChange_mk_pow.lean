-- Prove2me | solution 1 for FormalGroup.exists_lawIso_of_forall_isBaseChange_mk_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/014c9869-1fe2-53e8-ac94-ddad25c4417c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (F' F : FormalGroup R)
    (F'q Fq : ∀ n : ℕ, FormalGroup (R ⧸ maximalIdeal R ^ (n + 1)))
    (hF' : ∀ n : ℕ, F'.IsBaseChange (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (F'q n))
    (hF : ∀ n : ℕ, F.IsBaseChange (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (Fq n))
    (ψ : ∀ n : ℕ, FormalGroup.LawIso (F'q n) (Fq n))
    (hψ : ∀ n : ℕ, PowerSeries.map (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)))
      (ψ (n + 1)).series = (ψ n).series) :
    ∃ Ψ : FormalGroup.LawIso F' F, ∀ n : ℕ,
      PowerSeries.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) Ψ.series = (ψ n).series := by
  classical

  have hIle : ∀ n : ℕ, maximalIdeal R ^ (n + 1) ≤ maximalIdeal R := fun n =>
    Ideal.pow_le_self (Nat.succ_ne_zero n)
  have fac_mk : ∀ (n : ℕ) (r : R), Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))
      (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := fun n r => Ideal.Quotient.factor_mk _ _

  have hlift : ∀ (n : ℕ) (x : R ⧸ maximalIdeal R ^ (n + 1)), ∃ r : R, Ideal.Quotient.mk _ r = x :=
    fun n x => Ideal.Quotient.mk_surjective x
  choose lift hlift using hlift

  let f : ℕ → ℕ → R := fun m n => Nat.casesOn n 0 fun i => lift i (PowerSeries.coeff m (ψ i).series)
  have f_succ : ∀ m i, f m (i + 1) = lift i (PowerSeries.coeff m (ψ i).series) := fun m i => rfl
  have f_mk : ∀ m i, Ideal.Quotient.mk (maximalIdeal R ^ (i + 1)) (f m (i + 1)) =
      PowerSeries.coeff m (ψ i).series := fun m i => by rw [f_succ, hlift]
  have hcauchy : ∀ m, AdicCompletion.IsAdicCauchy (maximalIdeal R) R (f m) := by
    intro m
    rw [AdicCompletion.isAdicCauchy_iff]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ i =>
      rw [← Ideal.Quotient.eq, f_mk, ← fac_mk, f_mk, ← PowerSeries.coeff_map, hψ i]
  have hlim : ∀ m, ∃ L : R, ∀ n, f m n ≡ L [SMOD (maximalIdeal R ^ n • ⊤ : Submodule R R)] :=
    fun m => IsPrecomplete.prec inferInstance (hcauchy m)
  choose L hL using hlim
  have hL' : ∀ (m i : ℕ), Ideal.Quotient.mk (maximalIdeal R ^ (i + 1)) (L m) = PowerSeries.coeff m (ψ i).series := by
    intro m i
    have h := hL m (i + 1)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, f_mk] at h
    exact h.symm

  let Ψs : PowerSeries R := PowerSeries.mk (L ·)
  have hΨn : ∀ n : ℕ, PowerSeries.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) Ψs = (ψ n).series := by
    intro n; ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hL']

  have hΨ0 : PowerSeries.constantCoeff Ψs = 0 := by
    refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ i =>
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_mk, hL', PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (ψ i).constantCoeff_series

  have hF's : PowerSeries.HasSubst F'.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero F'.zero_constantCoeff
  have hXi : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hsX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (FormalGroup.LawHom.substX i Ψs) = 0 := by
    intro i; unfold FormalGroup.LawHom.substX
    exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hΨ0
  have hS : MvPowerSeries.HasSubst (![FormalGroup.LawHom.substX 0 Ψs, FormalGroup.LawHom.substX 1 Ψs] :
      Fin 2 → MvPowerSeries (Fin 2) R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hsX 0, hsX 1⟩)
  have hcomm : PowerSeries.subst F'.toPowerSeries Ψs =
      MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 Ψs, FormalGroup.LawHom.substX 1 Ψs] F.toPowerSeries := by
    ext e
    refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ i =>
      rw [← Ideal.Quotient.eq, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map]
      congr 1

      have eF' := hF' i
      have eF := hF i
      unfold FormalGroup.IsBaseChange at eF' eF
      have eX : ∀ j : Fin 2, MvPowerSeries.map (Ideal.Quotient.mk (maximalIdeal R ^ (i + 1)))
          (FormalGroup.LawHom.substX j Ψs) = FormalGroup.LawHom.substX j (ψ i).series := by
        intro j; unfold FormalGroup.LawHom.substX
        rw [PowerSeries.map_subst (hXi j), MvPowerSeries.map_X, hΨn]
      rw [PowerSeries.map_subst hF's, ← eF', hΨn, (ψ i).comm, MvPowerSeries.map_subst hS, ← eF]
      congr 1
      funext j
      fin_cases j
      · exact (eX 0).symm
      · exact (eX 1).symm

  have hunit : IsUnit (PowerSeries.coeff 1 Ψs) := by
    by_contra hu
    have hmem : PowerSeries.coeff 1 Ψs ∈ maximalIdeal R ^ (0 + 1) := by
      rw [_root_.zero_add, pow_one]; exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h0 : PowerSeries.coeff 1 (ψ 0).series = 0 := by
      rw [← hΨn 0, PowerSeries.coeff_map]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have h1 := (ψ 0).isUnit_coeff_one
    rw [h0, isUnit_zero_iff] at h1
    haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIle 0))
    exact zero_ne_one h1
  exact ⟨⟨⟨Ψs, hΨ0, hcomm⟩, hunit⟩, hΨn⟩

end S_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow
end P2MW
export P2MW.S_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow (solution)
