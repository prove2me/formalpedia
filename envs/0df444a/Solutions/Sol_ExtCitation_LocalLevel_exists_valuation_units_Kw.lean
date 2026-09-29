-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_valuation_units_Kw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1671f8a1-24a3-549d-bf82-33273eef1ee2

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_valuation_units_Kw

set_option autoImplicit false
open ExtCitation.LocalLevel
open scoped NNReal

namespace Ws26T4D
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem mem_Rw_iff_norm_le_one (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem norm_coe_eq_spectralNorm (x : Kw) : ‖(x : PadicAlgCl q)‖ = spectralNorm ℚ_[q] Kw x := by
  rw [spectralNorm.eq_of_tower (L := PadicAlgCl q), PadicAlgCl.spectralNorm_eq]; rfl

end Ws26T4D

namespace Ws26T4
open ExtCitation.LocalLevel IsLocalRing

section Relative
variable (q : ℕ) [Fact q.Prime] (Kw Lw : IntermediateField ℚ_[q] (PadicAlgCl q))
  [FiniteDimensional ℚ_[q] Kw] [FiniteDimensional ℚ_[q] Lw] (hKL : Kw ≤ Lw)

noncomputable def inclRw : Rw q Kw →+* Rw q Lw where
  toFun x := ⟨IntermediateField.inclusion hKL x, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_inclRw (x : Rw q Kw) :
    (((inclRw q Kw Lw hKL x : Rw q Lw) : Lw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) := rfl

omit [FiniteDimensional ℚ_[q] Kw] in

theorem isUnit_of_norm_eq_one {x : Rw q Kw} (hx : ‖((x : Kw) : PadicAlgCl q)‖ = 1) : IsUnit x := by
  have hx0 : (x : Kw) ≠ 0 := by
    intro h
    have : ((x : Kw) : PadicAlgCl q) = 0 := by rw [h]; rfl
    rw [this, norm_zero] at hx; exact zero_ne_one hx
  have hinv : (x : Kw)⁻¹ ∈ Rw q Kw := by
    show ‖(((x : Kw)⁻¹ : Kw) : PadicAlgCl q)‖₊ ≤ 1
    have : (((x : Kw)⁻¹ : Kw) : PadicAlgCl q) = (((x : Kw) : PadicAlgCl q))⁻¹ := by push_cast; rfl
    rw [this, nnnorm_inv]
    have hx' : ‖((x : Kw) : PadicAlgCl q)‖₊ = 1 := by ext; exact hx
    rw [hx', inv_one]
  refine ⟨⟨x, ⟨(x : Kw)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

end Relative
end Ws26T4

open Ws26T4 Ws26T4D ExtCitation.LocalLevel IsDedekindDomain in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ v : (↥Kw)ˣ →* Multiplicative ℤ, Function.Surjective v ∧
      (∀ x : (↥Kw)ˣ, v x = 1 ↔ ((x : Kw) ∈ Rw q Kw ∧ ((x⁻¹ : (↥Kw)ˣ) : Kw) ∈ Rw q Kw)) ∧
      (∀ (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : (↥Kw)ˣ), v (Units.map (σ : Kw →* Kw) x) = v x) ∧
      (∀ x : (↥Kw)ˣ, (x : Kw) ∈ Rw q Kw → v x ≤ 1) := by
  classical
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  set w : HeightOneSpectrum (Rw q Kw) := IsDiscreteValuationRing.maximalIdeal (Rw q Kw) with hw
  have hall : ∀ w' : HeightOneSpectrum (Rw q Kw), w' = w := fun w' =>
    HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (w'.isPrime.isMaximal w'.ne_bot))
  let val : Valuation Kw (WithZero (Multiplicative ℤ)) := w.valuation Kw
  let v : (↥Kw)ˣ →* Multiplicative ℤ := w.valuationOfNeZero (K := (Kw : Type))
  have hv : ∀ x : (↥Kw)ˣ, (v x : WithZero (Multiplicative ℤ)) = val (x : Kw) := fun x =>
    HeightOneSpectrum.valuationOfNeZero_eq w x

  have hmem_of_le : ∀ y : Kw, val y ≤ 1 → y ∈ Rw q Kw := by
    intro y hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (Kw : Type) y
      (fun w' => by rw [hall w']; exact hy)
    rw [← hr]; exact r.2
  have hle_of_mem : ∀ y : Kw, y ∈ Rw q Kw → val y ≤ 1 := fun y hy =>
    HeightOneSpectrum.valuation_le_one w ⟨y, hy⟩

  have hker : ∀ x : (↥Kw)ˣ, v x = 1 ↔ ((x : Kw) ∈ Rw q Kw ∧ ((x⁻¹ : (↥Kw)ˣ) : Kw) ∈ Rw q Kw) := by
    intro x
    have hx0 : val (x : Kw) ≠ 0 := (Valuation.ne_zero_iff val).mpr x.ne_zero
    rw [← WithZero.coe_inj, hv, WithZero.coe_one]
    constructor
    · intro h
      refine ⟨hmem_of_le _ h.le, hmem_of_le _ ?_⟩
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
    · rintro ⟨h1, h2⟩
      refine le_antisymm (hle_of_mem _ h1) ?_
      have h3 := hle_of_mem _ h2
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h3
      exact (inv_le_one₀ (zero_lt_iff.mpr hx0)).mp h3

  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (Kw : Type) w
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  set πu : (↥Kw)ˣ := Units.mk0 π hπ0 with hπu
  have hvπ : v πu = Multiplicative.ofAdd (-1) := by
    rw [← WithZero.coe_inj, hv, hπu, Units.val_mk0, hπ]; rfl

  have hsurj : Function.Surjective v := by
    intro m
    refine ⟨πu ^ (-(Multiplicative.toAdd m)), ?_⟩
    rw [map_zpow, hvπ, ← ofAdd_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
    rfl

  have hnorm1 : ∀ y : (↥Kw)ˣ, v y = 1 → ‖((y : Kw) : PadicAlgCl q)‖ = 1 := by
    intro y hy
    obtain ⟨h1, h2⟩ := (hker y).mp hy
    have hn1 := (mem_Rw_iff_norm_le_one q Kw _).mp h1
    have hn2 := (mem_Rw_iff_norm_le_one q Kw _).mp h2
    rw [Units.val_inv_eq_inv_val] at hn2
    have hy0 : ((y : Kw) : PadicAlgCl q) ≠ 0 := by
      intro h; exact y.ne_zero (by exact_mod_cast h)
    have : ((((y : Kw)⁻¹ : Kw)) : PadicAlgCl q) = (((y : Kw) : PadicAlgCl q))⁻¹ := by push_cast; rfl
    rw [this, norm_inv] at hn2
    have hpos : 0 < ‖((y : Kw) : PadicAlgCl q)‖ := norm_pos_iff.mpr hy0
    exact le_antisymm hn1 ((inv_le_one₀ hpos).mp hn2)
  have hnormπ_pos : 0 < ‖(π : PadicAlgCl q)‖ := norm_pos_iff.mpr (by intro h; exact hπ0 (by exact_mod_cast h))
  have hnormπ_ne_one : ‖(π : PadicAlgCl q)‖ ≠ 1 := by
    intro h1

    have hπle : val π ≤ 1 := by rw [hπ]; exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num) |>.trans_eq WithZero.exp_zero)
    have hπR : π ∈ Rw q Kw := hmem_of_le π hπle
    have hunit : IsUnit (⟨π, hπR⟩ : Rw q Kw) := isUnit_of_norm_eq_one q Kw (by exact h1)
    have hlt : val π < 1 := by rw [hπ, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hmem : (⟨π, hπR⟩ : Rw q Kw) ∈ w.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem w ⟨π, hπR⟩).mp hlt
    have : w.asIdeal = IsLocalRing.maximalIdeal (Rw q Kw) := rfl
    rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem hunit
  have hnorm : ∀ y : (↥Kw)ˣ, ‖((y : Kw) : PadicAlgCl q)‖ = ‖(π : PadicAlgCl q)‖ ^ (-(Multiplicative.toAdd (v y))) := by
    intro y
    set n : ℤ := Multiplicative.toAdd (v y) with hn
    have h1 : v (y * πu ^ n) = 1 := by
      rw [map_mul, map_zpow, hvπ, ← ofAdd_zsmul, smul_eq_mul, mul_neg, mul_one,
        show v y = Multiplicative.ofAdd n by rw [hn, ofAdd_toAdd], ← ofAdd_add, add_neg_cancel, ofAdd_zero]
    have h2 := hnorm1 _ h1
    have hcoe : (((y * πu ^ n : (↥Kw)ˣ) : Kw) : PadicAlgCl q) = ((y : Kw) : PadicAlgCl q) * (π : PadicAlgCl q) ^ n := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hπu, Units.val_mk0]; push_cast; rfl
    rw [hcoe, norm_mul, norm_zpow] at h2
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h2

  have hgal : ∀ (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : (↥Kw)ˣ), v (Units.map (σ : Kw →* Kw) x) = v x := by
    intro σ x
    have h1 := hnorm (Units.map (σ : Kw →* Kw) x)
    have h2 := hnorm x
    have hσ : ‖(((Units.map (σ : Kw →* Kw) x : (↥Kw)ˣ) : Kw) : PadicAlgCl q)‖ = ‖((x : Kw) : PadicAlgCl q)‖ := by
      rw [Units.coe_map, MonoidHom.coe_coe, norm_coe_eq_spectralNorm, norm_coe_eq_spectralNorm,
        ← spectralNorm_eq_of_equiv σ]
    rw [hσ, h2] at h1
    have h3 := (zpow_right_injective₀ hnormπ_pos hnormπ_ne_one) h1
    simp only [neg_inj] at h3
    exact (Multiplicative.toAdd.injective h3).symm
  refine ⟨v, hsurj, hker, hgal, fun x hx => ?_⟩
  rw [← WithZero.coe_le_coe, hv, WithZero.coe_one]
  exact hle_of_mem _ hx

end S_ExtCitation_LocalLevel_exists_valuation_units_Kw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_valuation_units_Kw (solution)
