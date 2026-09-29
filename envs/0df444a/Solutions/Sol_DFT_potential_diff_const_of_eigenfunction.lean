-- Prove2me | solution 1 for DFT.potential_diff_const_of_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:38:19.194645+00:00
-- url     : https://prove2.me/submissions/a2dc8b10-e988-4667-9747-f8b42e8e8bca

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

namespace Ag3Aux_PotConst

theorem mp (n : ℕ) (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i)
      (volume : Measure (Config n)) ((volume : Measure Pos).prod (volume : Measure (Fin n → Pos))) :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i

theorem symm_apply (n : ℕ) (i : Fin (n + 1)) (p : Pos × (Fin n → Pos)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i).symm p = i.insertNth p.1 p.2 :=
  rfl

end Ag3Aux_PotConst

open Ag3Aux_PotConst

theorem solution {n : ℕ} (w : Pos → ℝ) (hw : Measurable w)
    (c : ℝ) (Ψ : Config n → ℂ) (hΨ : ∀ᵐ x, Ψ x ≠ 0)
    (heq : ∀ᵐ x, (∑ i, w (x i)) • Ψ x = c • Ψ x) :
    ∀ᵐ r, w r = c / (n + 1) := by
  have hsum : ∀ᵐ x : Config n, ∑ i, w (x i) = c := by
    filter_upwards [hΨ, heq] with x h1 h2
    have : ((∑ i, w (x i)) - c) • Ψ x = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h h1
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) 0
  have hprod : ∀ᵐ p ∂((volume : Measure Pos).prod (volume : Measure (Fin n → Pos))),
      w p.1 + ∑ j, w (p.2 j) = c := by
    have := (mp n 0).symm.quasiMeasurePreserving.ae hsum
    filter_upwards [this] with p hp
    rw [symm_apply, Fin.sum_univ_succAbove _ 0] at hp
    simpa [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using hp
  have hae := Measure.ae_ae_of_ae_prod hprod
  obtain ⟨r0, hr0⟩ := hae.exists
  have hconst : ∀ᵐ r : Pos, w r = w r0 := by
    filter_upwards [hae] with r hr
    obtain ⟨y, hy1, hy2⟩ := (hr.and hr0).exists
    linarith
  have hall : ∀ᵐ x : Config n, ∀ i, w (x i) = w r0 := by
    rw [ae_all_iff]
    intro i
    have h1 : ∀ᵐ p ∂((volume : Measure Pos).prod (volume : Measure (Fin n → Pos))), w p.1 = w r0 :=
      Measure.quasiMeasurePreserving_fst.ae hconst
    have := (mp n i).quasiMeasurePreserving.ae h1
    filter_upwards [this] with x hx
    simpa using hx
  obtain ⟨x, hx1, hx2⟩ := (hsum.and hall).exists
  simp only [hx2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hx1
  filter_upwards [hconst] with r hr
  rw [hr, ← hx1]
  push_cast
  field_simp
