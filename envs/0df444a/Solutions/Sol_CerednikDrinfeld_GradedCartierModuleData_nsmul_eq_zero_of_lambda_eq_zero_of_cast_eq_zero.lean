-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/921d1e87-4cc3-5dbc-b23c-a444844d362e

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) (hp : (p : B) = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (z : D.NMod) (hz : D.lambda z = 0) :
    p • z = 0 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  ·
    haveI : Subsingleton (WittVector p B) := ⟨fun a b => WittVector.ext fun n => Subsingleton.elim _ _⟩
    have : z = 0 := by
      rw [← one_smul (WittVector p B) z, Subsingleton.elim (1 : WittVector p B) 0, zero_smul]
    rw [this, nsmul_zero]
  haveI : CharP B p := by
    have := CharP.exists B
    obtain ⟨q, hq⟩ := this
    have hdvd : q ∣ p := (CharP.cast_eq_zero_iff B q p).1 hp
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | h2
    · subst h1
      have h10 : ((1 : ℕ) : B) = 0 := (CharP.cast_eq_zero_iff B 1 1).2 (dvd_refl 1)
      exact absurd h10 (by rw [Nat.cast_one]; exact one_ne_zero)
    · subst h2; exact hq
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [lambda_nMk] at hz

  have hpW : ((p : ℕ) : WittVector p B) = WittVector.verschiebung 1 := by
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero]; exact WittVector.coeff_p_zero (p := p) (R := B)
    | succ n =>
      rw [WittVector.verschiebung_coeff_succ]
      cases n with
      | zero => rw [WittVector.coeff_p_one]; simp
      | succ n => rw [WittVector.coeff_p (p := p) (R := B)]; simp
  have hpm : (p : ℕ) • m = D.verschiebung (D.frobenius m) := by
    have h := D.verschiebung_smul_frobenius 1 m
    rw [one_smul, ← hpW, Nat.cast_smul_eq_nsmul] at h
    exact h.symm
  have hPm : D.varpi (D.frobenius m) = -((p : ℕ) • m') := by
    rw [D.varpi_frobenius, eq_neg_iff_add_eq_zero, ← D.frobenius_verschiebung, ← map_add, hz, map_zero]
  rw [← map_nsmul, Prod.smul_mk, hpm]
  have : ((p : ℕ) • m' : D.M) = -D.varpi (D.frobenius m) := by rw [hPm, neg_neg]
  rw [this]
  exact D.nMk_verschiebung_neg_varpi _

end S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero (solution)
