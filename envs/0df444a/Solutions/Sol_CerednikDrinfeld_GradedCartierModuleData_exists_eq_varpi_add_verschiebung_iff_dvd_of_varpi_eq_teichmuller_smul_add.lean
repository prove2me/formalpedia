-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a9b08a45-32ef-566b-a3c2-d1597b4a5a66

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add

set_option autoImplicit false

open CerednikDrinfeld

namespace PiRangeDigit

open CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem exists_eq_teichmuller_smul_add_verschiebung {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  classical
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x
  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hy
  fin_cases i
  · have hdec : x = (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) +
        (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have hz : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 0 := by
      have : x - (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) ∈ D.piece 0 := Submodule.sub_mem _ hx h0
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ hz h1
    refine ⟨c 0, y1, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl
  · have hdec : x = (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) +
        (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have hz : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 1 := by
      have : x - (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) ∈ D.piece 1 := Submodule.sub_mem _ hx h1
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ h0 hz
    refine ⟨c 1, y0, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl

theorem teichmuller_coeff_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (c c' : Fin 2 → B) (y y' : D.M)
    (h : (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (c' i) • γ i) + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y)
  have h1 : (c, y) = cy := huniq (c, y) rfl
  have h2 : (c', y') = cy := huniq (c', y') h
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem sum_single (γ : Fin 2 → D.M) (i : Fin 2) (c : B) :
    (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i c : Fin 2 → B) k) • γ k) =
      WittVector.teichmuller p c • γ i := by
  classical
  rw [Fintype.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k hk
    rw [Pi.single_eq_of_ne hk, WittVector.teichmuller_zero, zero_smul]

end PiRangeDigit

open PiRangeDigit in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xnext : D.M) (a : B)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (c : B) (n : D.M) :
    (∃ x ∈ D.piece (i + 1), ∃ x' : D.M,
        WittVector.teichmuller p c • γ i + D.verschiebung n = D.varpi x + D.verschiebung x') ↔ a ∣ c := by
  classical

  have hPi : ∀ (s : B) (y : D.M),
      D.varpi (WittVector.teichmuller p s • γ (i + 1) + D.verschiebung y) =
        WittVector.teichmuller p (s * a) • γ i +
          D.verschiebung (WittVector.frobenius (WittVector.teichmuller p s) • xnext + D.varpi y) := by
    intro s y
    rw [map_add, map_smul, hnext, D.varpi_verschiebung, smul_add, smul_smul, ← map_mul,
      D.smul_verschiebung, add_assoc, ← map_add]
  constructor
  · rintro ⟨x, hx, x', hxe⟩
    obtain ⟨s, y, rfl⟩ := exists_eq_teichmuller_smul_add_verschiebung D hγ (i + 1) x hx
    rw [hPi, add_assoc, ← map_add, ← sum_single D γ i c, ← sum_single D γ i (s * a)] at hxe
    obtain ⟨hc, -⟩ := teichmuller_coeff_unique D hγ _ _ _ _ hxe
    have hci := congrFun hc i
    simp only [Pi.single_eq_same] at hci
    exact ⟨s, hci.trans (mul_comm s a)⟩
  · rintro ⟨s, rfl⟩
    refine ⟨WittVector.teichmuller p s • γ (i + 1), Submodule.smul_mem _ _ (hγ.1 (i + 1)),
      n - WittVector.frobenius (WittVector.teichmuller p s) • xnext, ?_⟩
    have h := hPi s 0
    rw [map_zero, add_zero, map_zero, add_zero] at h
    rw [h, add_assoc, ← map_add, add_sub_cancel, mul_comm]

end S_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add (solution)
