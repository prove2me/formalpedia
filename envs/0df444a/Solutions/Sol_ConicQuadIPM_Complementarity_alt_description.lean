-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.alt_description
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:11:13.607092+00:00
-- url     : https://prove2.me/submissions/7d5da42b-c10e-40ae-8e30-8d99f8dc3252

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000

private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp


private lemma qrot_action (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Qmat .rot d *ᵥ v) a = if a.val = 0 then coord v 1 else if a.val = 1 then coord v 0 else -v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Qmat .rot d a j * v j) = _
  by_cases h0 : a.val = 0
  · rw [Finset.sum_eq_single o]
    · simp [Qmat, h0, z, o, coordinate v 1 (by omega)]
    · intro j hj hjo
      have hn : j.val ≠ 1 := by intro he; apply hjo; exact Fin.ext he
      simp [Qmat, h0, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp
  · by_cases h1 : a.val = 1
    · rw [Finset.sum_eq_single z]
      · simp [Qmat, h1, z, o, coordinate v 0 (by omega)]
      · intro j hj hjz
        have hn : j.val ≠ 0 := by intro he; apply hjz; exact Fin.ext he
        simp [Qmat, h1, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp [Qmat, h0, h1, show ¬ a.val < 2 by omega]
      · intro j hj hja
        simp [Qmat, show ¬ a.val < 2 by omega, Ne.symm hja]
      · simp

private lemma quad_form (d : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .quad d *ᵥ v) = coord v 0 ^ 2 - tailSq v 1 := by
  have hhead : (∑ j : Fin d, if j.val = 0 then v j ^ 2 else 0) = coord v 0 ^ 2 := by
    cases d with
    | zero => simp [coord]
    | succ d =>
      rw [coordinate v 0 (by omega), Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj h; simp [show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
      · simp
  change (∑ j : Fin d, v j * (Qmat .quad d *ᵥ v) j) = _
  have he : ∀ j : Fin d, v j * (Qmat .quad d *ᵥ v) j =
      (if j.val = 0 then v j ^ 2 else 0) - (if 1 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    simp only [Qmat, Matrix.mulVec_diagonal]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hhead]; rfl

private lemma rot_form (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .rot d *ᵥ v) = 2 * coord v 0 * coord v 1 - tailSq v 2 := by
  have he : ∀ j : Fin d, v j * (Qmat .rot d *ᵥ v) j =
      (if j = (⟨0, by omega⟩ : Fin d) then v j * coord v 1 else 0) +
      (if j = (⟨1, by omega⟩ : Fin d) then v j * coord v 0 else 0) -
      (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    rw [qrot_action d hd]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  change (∑ j : Fin d, v j * (Qmat .rot d *ᵥ v) j) = _
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← coordinate v 0 (by omega), ← coordinate v 1 (by omega)]
  unfold tailSq; ring

theorem solution (d : ℕ) (v : Fin d → ℝ) :
    (inQuad v ↔ 0 ≤ v ⬝ᵥ (Qmat .quad d *ᵥ v) ∧ 0 ≤ coord v 0) ∧
    (2 ≤ d → (inRot v ↔
      0 ≤ v ⬝ᵥ (Qmat .rot d *ᵥ v) ∧ 0 ≤ coord v 0 ∧ 0 ≤ coord v 1)) := by
  constructor
  · rw [quad_form]
    unfold inQuad
    constructor <;> rintro ⟨h, hn⟩ <;> exact ⟨by linarith, hn⟩
  · intro hd
    rw [rot_form d hd]
    unfold inRot
    constructor <;> rintro ⟨h, hn⟩ <;> exact ⟨by linarith, hn⟩

#print axioms solution
