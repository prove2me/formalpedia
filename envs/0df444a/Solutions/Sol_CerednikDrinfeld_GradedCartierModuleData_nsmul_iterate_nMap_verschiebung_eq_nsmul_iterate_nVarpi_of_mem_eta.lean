-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3f1a79f1-2f67-5ec4-9dab-fbe558181fd3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta

set_option autoImplicit false

open CerednikDrinfeld

namespace EtaNV
open CerednikDrinfeld
variable {p : ℕ} [hp : Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nsmul_nMk (D : GradedCartierModuleData p B j) (n : ℕ) (x y : D.M) :
    n • D.nMk (x, y) = D.nMk (n • x, n • y) := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nMk (D : GradedCartierModuleData p B j) (x y : D.M) :
    D.nVarpi (D.nMk (x, y)) = D.nMk (D.varpi x, D.varpi y) := rfl

theorem nMk_sub (D : GradedCartierModuleData p B j) (x y x' y' : D.M) :
    D.nMk (x, y) - D.nMk (x', y') = D.nMk (x - x', y - y') := by
  rw [← map_sub]; rfl

theorem nsmul_eq_zero_of_lambda_eq_zero (D : GradedCartierModuleData p B j)
    (hVF : ∀ m : D.M, D.verschiebung (D.frobenius m) = (p : ℕ) • m)
    (z : D.NMod) (hz : D.lambda z = 0) : (p : ℕ) • z = 0 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [GradedCartierModuleData.lambda_nMk] at hz
  rw [nsmul_nMk, ← hVF a, ← D.frobenius_verschiebung b]

  have h1 : D.nMk (D.verschiebung (D.frobenius a), D.frobenius (D.verschiebung b)) =
      D.nMk (0, D.varpi (D.frobenius a) + D.frobenius (D.verschiebung b)) := by
    have hrel := D.nMk_verschiebung_neg_varpi (D.frobenius a)
    have : D.nMk (D.verschiebung (D.frobenius a), D.frobenius (D.verschiebung b)) =
        D.nMk (D.verschiebung (D.frobenius a), -D.varpi (D.frobenius a)) +
          D.nMk (0, D.varpi (D.frobenius a) + D.frobenius (D.verschiebung b)) := by
      rw [← map_add, Prod.mk_add_mk, add_zero]
      congr 1
      ext <;> simp
    rw [this, hrel, zero_add]
  rw [h1, D.varpi_frobenius, ← map_add, hz, map_zero]
  have : D.nMk (0, 0) = 0 := map_zero D.nMk
  exact this

theorem verschiebung_lambda_eq_varpi_lambda (D : GradedCartierModuleData p B j)
    (hVF : ∀ m : D.M, D.verschiebung (D.frobenius m) = (p : ℕ) • m)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (y : D.NMod) (hy : y ∈ D.eta L hL.map_verschiebung) :
    D.verschiebung (D.lambda y) = D.varpi (D.lambda y) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective y
  rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk] at hy

  have key := congrArg D.lambda hy
  rw [map_add, hL.lambda_comp, GradedCartierModuleData.lambda_nMk, GradedCartierModuleData.lambda_nMk,
    map_zero, add_zero] at key
  rw [GradedCartierModuleData.lambda_nMk, map_add, map_add, D.varpi_varpi, D.varpi_verschiebung,
    ← map_add D.verschiebung, ← key, map_add, hVF]

theorem main (D : GradedCartierModuleData p B j)
    (hVF : ∀ m : D.M, D.verschiebung (D.frobenius m) = (p : ℕ) • m)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (NV : D.NMod →+ D.NMod) (hNV : ∀ x y : D.M, NV (D.nMk (x, y)) = D.nMk (D.verschiebung x, D.verschiebung y))
    (m : ℕ) (y : D.NMod) (hy : y ∈ D.eta L hL.map_verschiebung) :
    (p : ℕ) • ((⇑NV)^[m] y) = (p : ℕ) • ((⇑D.nVarpi)^[m] y) := by

  have one : ∀ y : D.NMod, y ∈ D.eta L hL.map_verschiebung → (p : ℕ) • NV y = (p : ℕ) • D.nVarpi y := by
    intro y hy
    have hVl := verschiebung_lambda_eq_varpi_lambda D hVF L hL y hy
    obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective y
    rw [hNV, nVarpi_nMk, ← sub_eq_zero, ← nsmul_sub, nMk_sub]
    apply nsmul_eq_zero_of_lambda_eq_zero D hVF
    rw [GradedCartierModuleData.lambda_nMk, map_sub, map_sub, D.varpi_verschiebung, D.varpi_varpi]
    rw [GradedCartierModuleData.lambda_nMk, map_add, map_add, D.varpi_varpi, D.varpi_verschiebung] at hVl

    have : D.verschiebung (D.varpi x) - (p : ℕ) • x + (D.verschiebung (D.verschiebung x') - D.verschiebung (D.varpi x')) =
        (D.verschiebung (D.varpi x) + D.verschiebung (D.verschiebung x')) - ((p : ℕ) • x + D.verschiebung (D.varpi x')) := by
      abel
    rw [this, hVl, sub_self]

  have comm : ∀ z : D.NMod, NV (D.nVarpi z) = D.nVarpi (NV z) := by
    intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
    rw [nVarpi_nMk, hNV, hNV, nVarpi_nMk, D.varpi_verschiebung, D.varpi_verschiebung]
  have commIter : ∀ (n : ℕ) (z : D.NMod), NV ((⇑D.nVarpi)^[n] z) = (⇑D.nVarpi)^[n] (NV z) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih => intro z; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', comm, ih]
  have iterNsmul : ∀ (n : ℕ) (w : D.NMod), (⇑D.nVarpi)^[n] ((p : ℕ) • w) = (p : ℕ) • (⇑D.nVarpi)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_nsmul]
  induction m with
  | zero => rfl
  | succ m ih =>
    calc (p : ℕ) • ((⇑NV)^[m + 1] y) = NV ((p : ℕ) • ((⇑NV)^[m] y)) := by
            rw [Function.iterate_succ_apply', map_nsmul]
      _ = NV ((p : ℕ) • ((⇑D.nVarpi)^[m] y)) := by rw [ih]
      _ = (⇑D.nVarpi)^[m] ((p : ℕ) • NV y) := by rw [map_nsmul, commIter, iterNsmul]
      _ = (⇑D.nVarpi)^[m] ((p : ℕ) • D.nVarpi y) := by rw [one y hy]
      _ = (p : ℕ) • ((⇑D.nVarpi)^[m + 1] y) := by rw [iterNsmul, Function.iterate_succ_apply]

end EtaNV

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j)
    (hVF : ∀ m : D.M, D.verschiebung (D.frobenius m) = (p : ℕ) • m)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (NV : D.NMod →+ D.NMod)
    (hNV : ∀ x y : D.M, NV (D.nMk (x, y)) = D.nMk (D.verschiebung x, D.verschiebung y))
    (m : ℕ) (y : D.NMod) (hy : y ∈ D.eta L hL.map_verschiebung) :
    (p : ℕ) • ((⇑NV)^[m] y) = (p : ℕ) • ((⇑D.nVarpi)^[m] y) :=
  EtaNV.main D hVF L hL NV hNV m y hy

end S_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta (solution)
