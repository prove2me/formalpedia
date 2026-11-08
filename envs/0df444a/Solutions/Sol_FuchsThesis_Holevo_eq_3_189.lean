-- Prove2me | solution 1 for FuchsThesis.Holevo.eq_3_189
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:38:18.238273+00:00
-- url     : https://prove2.me/submissions/3ca4a720-53cb-4bd1-86b5-b685ae35f4e2

import Mathlib
import Definitions.Def_FuchsThesis_Holevo_phi

namespace Aux_FuchsThesis_Holevo_eq_3_189

lemma key (t : ℝ) (ht : 1 < t) : 2 * (t - 1) / (t + 1) < Real.log t := by
  let f : ℝ → ℝ := fun s => Real.log s - 2 * (s - 1) / (s + 1)
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt f (s⁻¹ - (2 * 1 * (s + 1) - 2 * (s - 1) * 1) / (s + 1) ^ 2) s := by
    intro s hs
    have h1 := Real.hasDerivAt_log hs.ne'
    have h2 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) (2 * 1) s :=
      ((hasDerivAt_id s).sub_const 1).const_mul 2
    have h3 : HasDerivAt (fun s : ℝ => s + 1) 1 s := (hasDerivAt_id s).add_const 1
    exact h1.sub (h2.div h3 (by linarith))
  have hcont : ContinuousOn f (Set.Ici 1) := by
    intro s hs
    exact (hd s (by linarith [Set.mem_Ici.mp hs])).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1) hcont
    intro s hs
    rw [interior_Ici] at hs
    have hs1 : 1 < s := hs
    rw [(hd s (by linarith)).deriv]
    have e : s⁻¹ - (2 * 1 * (s + 1) - 2 * (s - 1) * 1) / (s + 1) ^ 2
        = (s - 1) ^ 2 / (s * (s + 1) ^ 2) := by
      field_simp <;> ring
    rw [e]
    have : 0 < s - 1 := by linarith
    positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht
  simp only [f, Real.log_one, sub_self, zero_mul, zero_div] at this
  linarith

lemma key2 (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    2 * (a - b) / (a + b) < Real.log a - Real.log b := by
  have ha : 0 < a := by linarith
  rw [← Real.log_div ha.ne' hb.ne']
  have h := key (a / b) (by rw [lt_div_iff₀ hb]; linarith)
  have e : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    field_simp <;> ring
  rw [e] at h
  exact h

end Aux_FuchsThesis_Holevo_eq_3_189

open FuchsThesis.Holevo Aux_FuchsThesis_Holevo_eq_3_189 in
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / (x + y) ≤ phi x y ∧ (phi x y = 2 / (x + y) ↔ x = y) := by
  have hstrict : x ≠ y → 2 / (x + y) < phi x y := by
    intro hne
    unfold phi
    rw [if_neg hne]
    rcases lt_or_gt_of_ne hne with h | h
    · have k := key2 y x hx h
      have hyx : 0 < y - x := by linarith
      rw [lt_div_iff_of_neg (by linarith)]
      have e : 2 / (x + y) * (x - y) = -(2 * (y - x) / (y + x)) := by
        field_simp <;> ring
      rw [e]
      linarith
    · have k := key2 x y hy h
      rw [lt_div_iff₀ (by linarith)]
      have e : 2 / (x + y) * (x - y) = 2 * (x - y) / (x + y) := by ring
      rw [e]
      exact k
  by_cases hxy : x = y
  · subst hxy
    have hp : phi x x = 2 / (x + x) := by
      unfold phi; rw [if_pos rfl]; field_simp <;> ring
    exact ⟨le_of_eq hp.symm, ⟨fun _ => rfl, fun _ => hp⟩⟩
  · have := hstrict hxy
    exact ⟨this.le, ⟨fun h => absurd h this.ne', fun h => absurd h hxy⟩⟩
