-- Prove2me | solution 1 for CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ba4ba50d-6099-59e3-a61c-1d6a67422018

import Mathlib
import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
import Theorems.Thm_CohCarrier_iDeg_comp
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"

set_option autoImplicit false

p2m_open "CohCarrier P2MW.S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant.CohCarrier CongruenceSubgroup"
open scoped MatrixGroups

namespace CohCarrier p2m_export "CohCarrier" "IsEis H1 diamondRaw LevelLE iDeg' injective_iDeg_one_and_range_eq_of_isUnit_index iDeg_comp iDeg_heckeT_comm_of_coprime" end CohCarrier
p2m_open_scoped "CohCarrier" in

theorem CohCarrier.iDeg'_congr_d {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {A : Type} [AddCommGroup A]
    [NeZero M'] {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (hd : d₁ = d₂) (h₁ : LevelLE M M' H H' d₁) (h₂ : LevelLE M M' H H' d₂)
    (φ : H1 M H A) : iDeg' M M' H H' d₁ A h₁ φ = iDeg' M M' H H' d₂ A h₂ φ := by
  subst hd; rfl

theorem solution
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) (H' : Subgroup (ZMod (N * q))ˣ)
    (h₁ : LevelLE N (N * q) H H' 1) (hq : LevelLE N (N * q) H H' q)
    (h₁top : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqtop : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q)
    (hunit : IsUnit ((H.index : ℕ) : R)) (hunit' : IsUnit ((H'.index : ℕ) : R))
    (hihara_top : ∀ g₀ h₀ : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁top g₀ + iDeg' N (N * q) ⊤ ⊤ q A hqtop h₀ = 0 →
        IsEis R A N ⊤ ℓ₀ g₀ ∧ IsEis R A N ⊤ ℓ₀ h₀)
    (g h : H1 N H A)
    (hg : ∀ σ : Gamma0 N, diamondRaw N H A σ g = g) (hh : ∀ σ : Gamma0 N, diamondRaw N H A σ h = h)
    (hgh : iDeg' N (N * q) H H' 1 A h₁ g + iDeg' N (N * q) H H' q A hq h = 0) :
    IsEis R A N H ℓ₀ g ∧ IsEis R A N H ℓ₀ h := by

  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNq0 : 0 < N * q := Nat.pos_of_ne_zero (NeZero.ne (N * q))
  have hres : LevelLE N N (⊤ : Subgroup (ZMod N)ˣ) H 1 := ⟨dvd_refl N, by rw [Nat.div_self hN0], fun u _ => Subgroup.mem_top _⟩
  have hres' : LevelLE (N * q) (N * q) (⊤ : Subgroup (ZMod (N * q))ˣ) H' 1 :=
    ⟨dvd_refl _, by rw [Nat.div_self hNq0], fun u _ => Subgroup.mem_top _⟩

  have hm1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) H' (1 * 1) :=
    ⟨dvd_mul_right N q, by rw [mul_one]; exact one_dvd _, fun u _ => Subgroup.mem_top _⟩
  have hmq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) H' (1 * q) :=
    ⟨dvd_mul_right N q, by rw [one_mul, Nat.mul_div_cancel_left q hN0], fun u _ => Subgroup.mem_top _⟩
  have hmq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) H' (q * 1) :=
    ⟨dvd_mul_right N q, by rw [mul_one, Nat.mul_div_cancel_left q hN0], fun u _ => Subgroup.mem_top _⟩

  obtain ⟨-, hinj, hrange, -⟩ := CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index N H R A hres hunit
  obtain ⟨-, hinj', -, -⟩ := CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index (N * q) H' R A hres' hunit'
  have hg' : g ∈ Set.range (iDeg' N N ⊤ H 1 A hres) := by rw [hrange]; exact hg
  have hh' : h ∈ Set.range (iDeg' N N ⊤ H 1 A hres) := by rw [hrange]; exact hh
  obtain ⟨g₀, rfl⟩ := hg'
  obtain ⟨h₀, rfl⟩ := hh'

  have hker : iDeg' N (N * q) ⊤ ⊤ 1 A h₁top g₀ + iDeg' N (N * q) ⊤ ⊤ q A hqtop h₀ = 0 := by
    apply hinj'
    rw [map_add, map_zero]
    have e1 : iDeg' (N * q) (N * q) ⊤ H' 1 A hres' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁top g₀) =
        iDeg' N (N * q) H H' 1 A h₁ (iDeg' N N ⊤ H 1 A hres g₀) := by
      rw [← CohCarrier.iDeg_comp h₁top hres' hm1, ← CohCarrier.iDeg_comp hres h₁ hm1]
    have eq : iDeg' (N * q) (N * q) ⊤ H' 1 A hres' (iDeg' N (N * q) ⊤ ⊤ q A hqtop h₀) =
        iDeg' N (N * q) H H' q A hq (iDeg' N N ⊤ H 1 A hres h₀) := by
      haveI : NeZero (q * 1) := ⟨by rw [mul_one]; exact NeZero.ne q⟩
      haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact NeZero.ne q⟩
      have a := CohCarrier.iDeg_comp (A := A) hqtop hres' hmq' h₀
      have b := CohCarrier.iDeg_comp (A := A) hres hq hmq h₀

      have c : iDeg' N (N * q) ⊤ H' (q * 1) A hmq' h₀ = iDeg' N (N * q) ⊤ H' (1 * q) A hmq h₀ :=
        CohCarrier.iDeg'_congr_d (by ring) hmq' hmq h₀
      rw [← a, c, b]
    rw [e1, eq, hgh]
  obtain ⟨hEg, hEh⟩ := hihara_top g₀ h₀ hker
  have hℓN : ¬ ℓ₀ ∣ N := fun hd => hℓNq (dvd_mul_of_dvd_left hd q)

  have tr : ∀ φ₀ : H1 N ⊤ A, IsEis R A N ⊤ ℓ₀ φ₀ → IsEis R A N H ℓ₀ (iDeg' N N ⊤ H 1 A hres φ₀) := by
    intro φ₀ hφ
    rw [IsEis] at hφ ⊢
    rw [← CohCarrier.iDeg_heckeT_comm_of_coprime hres (Nat.coprime_one_right ℓ₀) hℓ hℓN φ₀, hφ]
    rfl
  exact ⟨tr g₀ hEg, tr h₀ hEh⟩

end S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
end P2MW
export P2MW.S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant (solution)
