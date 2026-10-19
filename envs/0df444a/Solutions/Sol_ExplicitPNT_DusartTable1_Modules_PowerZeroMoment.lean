-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.PowerZeroMoment
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:11:36.799362+00:00
-- url     : https://prove2.me/submissions/34741ba5-560b-4cb6-ad12-dd2fa2ac296d

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_absolute_inverse_cube (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 24 := by
  classical
  let Zp := Z.filter (fun ρ => 0 < ρ.im)
  let Zn := Z.filter (fun ρ => ¬0 < ρ.im)
  have hpos : ∀ ρ ∈ Zp, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    exact ⟨hZ ρ hmem, hγ⟩
  have hneg : ∀ ρ ∈ Zn, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ ρ.im < 0 := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    have hnt := hZ ρ hmem
    have hn : ρ.im ≠ 0 := by
      intro he
      have hh := DusartSmoothing.RvM.nontrivial_zero_abs_height ρ hnt
      rw [he, abs_zero] at hh
      linarith [Real.pi_pos]
    exact ⟨hnt, lt_of_le_of_ne (le_of_not_gt hγ) hn⟩
  let C := Zn.image (starRingEnd ℂ)
  have hC : ∀ ρ ∈ C, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hnt, him⟩ := hneg τ hτ
    refine ⟨⟨?_, by simpa using hnt.2.1, by simpa using hnt.2.2⟩, ?_⟩
    · rw [riemannZeta_conj, hnt.1, map_zero]
    · simpa using neg_pos.mpr him
  have hB := finite_positive_inverse_cube_bound C hC
  dsimp [C] at hB
  rw [Finset.sum_image (fun a _ b _ he => by
    have hh := congrArg (starRingEnd ℂ) he
    simpa using hh)] at hB
  have he : (∑ ρ ∈ Zn, (DusartSmoothing.RvM.zeroMult (starRingEnd ℂ ρ) : ℝ) *
      (1 / (starRingEnd ℂ ρ).im^3)) =
      ∑ ρ ∈ Zn, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hnt := (hneg ρ hρ).1
    have hne : ρ ≠ 1 := by
      intro h
      have hσ := hnt.2.2
      rw [h] at hσ
      norm_num at hσ
    rw [DusartSmoothing.RvM.zeroMult_conj ρ hne]
    simp only [Complex.conj_im, abs_of_neg (hneg ρ hρ).2]
  rw [he] at hB
  have hP : (∑ ρ ∈ Zp, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 12 := by
    calc
      _ = ∑ ρ ∈ Zp, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [abs_of_pos (hpos ρ hρ).2]
      _ ≤ 12 := finite_positive_inverse_cube_bound Zp hpos
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 < ρ.im)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3))
  change (∑ ρ ∈ Zp, _) + (∑ ρ ∈ Zn, _) = _ at hsplit
  linarith

end ExplicitPNT.DusartTable1

theorem solution :
∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 24 := by
  exact finite_absolute_inverse_cube
