-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.haSpanSt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:57.638044+00:00
-- url     : https://prove2.me/submissions/245683e7-8392-490e-a5fb-7739ebe0ff28

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_coeff_comp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_map_int_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_wsub_sat
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_exists_clear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
section Sub
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
end Sub
section Maps
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)
end Maps
section Comp
variable {K : Type} [Field K] [CharZero K] {σ : Type}
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
end Comp
section Up
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
end Up
section Poly
variable {L : Type}
end Poly
section Main
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
end Main
section Assembly
private theorem fix_sum_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) (z : ι → ℤ)
    (hz : ρ z = z) (j : ι) : z j = ∑ b, z b * ρ (Pi.single b 1) j := by
  have hz' : z = ∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc z j = ρ z j := (congrFun hz j).symm
    _ = ρ (∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ)) j := by rw [← hz']
    _ = ∑ b, z b * ρ (Pi.single b 1) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
end Assembly
end Formalism.L2.FormalSeriesBounds.HaP
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (hS : SatRetrSt) (hR : RowInvUpSt) : HaSpanSt := by
  unfold HaSpanSt
  intro Ty _ r n cc isX a K _ _ O P hP
  obtain ⟨hPH, hPO⟩ := hP
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = P.support := ⟨_, rfl⟩
  obtain ⟨ρ, hρW, hρfix⟩ := hS Bd (Wsub r n cc isX a Bd) (fun z x hz hx => wsub_sat r n cc isX a Bd z x hz hx)
  have key : ∀ j : Bd, coeff j.1 P = ∑ b : Bd, coeff b.1 P * ((ρ (Pi.single b 1) j : ℤ) : K) := by
    intro j
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun lam => ?_
    obtain ⟨N, hN, z, hz⟩ := exists_clear Bd (fun b => lam (coeff b.1 P))
    have hzW : z ∈ Wsub r n cc isX a Bd := by
      have e : map (Int.castRingHom ℚ) (poly Bd z) = (N : ℚ) • comp lam P := by
        ext m
        rw [coeff_map_poly, coeff_smul, coeff_comp, smul_eq_mul]
        split_ifs with h
        · simpa using hz ⟨m, h⟩
        · have h0 : coeff m P = 0 := by
            by_contra hc
            exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
          rw [h0, map_zero, mul_zero]
      show map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a
      rw [e]
      exact hha_smul r n ℚ cc isX a _ (comp_mem r n lam hPH)
    have hfix := fix_sum_lemma ρ z (hρfix z hzW) j
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hq : (z j : ℚ) = ∑ b, (z b : ℚ) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by exact_mod_cast hfix
    simp only [hz] at hq
    rw [map_sub, map_sum, sub_eq_zero]
    have hl : lam (coeff j.1 P) = ∑ b : Bd, lam (coeff b.1 P) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by
      apply mul_left_cancel₀ hN'
      rw [hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hl]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs : coeff b.1 P * ((ρ (Pi.single b 1) j : ℤ) : K) = (ρ (Pi.single b 1) j) • coeff b.1 P := by
      rw [zsmul_eq_mul, mul_comm]
    rw [hs, map_zsmul, zsmul_eq_mul, mul_comm]
  have hmain : P = ∑ b : Bd, coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) := by
    ext m
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map_poly, smul_eq_mul]
    by_cases h : m ∈ Bd
    · simp only [dif_pos h, eq_intCast]
      exact key ⟨m, h⟩
    · simp only [dif_neg h, mul_zero, Finset.sum_const_zero]
      by_contra hc
      exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
  have hsum : ∑ i : Fin (Fintype.card Bd), coeff ((Fintype.equivFin Bd).symm i).1 P •
      map (Int.castRingHom K) (poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1))) =
      ∑ b : Bd, coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) :=
    Equiv.sum_comp (Fintype.equivFin Bd).symm
      (fun b : Bd => coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))))
  refine ⟨Fintype.card Bd, fun i => coeff ((Fintype.equivFin Bd).symm i).1 P,
    fun i => poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1)), fun i => hPO _,
    fun i K' _ _ => map_int_mem hR K' _ (hρW _), ?_⟩
  exact hmain.trans hsum.symm
end Formalism.L2.FormalSeriesBounds.HaP
