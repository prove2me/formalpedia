-- Prove2me | solution 1 for Erdos195.epsLt_safe_flip_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T04:35:04.9447+00:00
-- url     : https://prove2.me/submissions/922bd4f9-5063-40d7-95c6-3a07fc475e33

import Mathlib
import Definitions.Def_Erdos195_defs


namespace E195S52
open Erdos195

lemma div_flip (x : ℤ) (k : ℕ) : (-1 - x) / 2 ^ k = -1 - x / 2 ^ k := by
  have hp : (0:ℤ) < 2 ^ k := by positivity
  have h1 := Int.emod_nonneg x hp.ne'
  have h2 := Int.emod_lt_of_pos x hp
  have h3 := Int.mul_ediv_add_emod x (2 ^ k)
  have := (Int.ediv_emod_unique (a := -1 - x) (r := 2 ^ k - 1 - x % 2 ^ k) (q := -1 - x / 2 ^ k) hp).2
    ⟨by linear_combination (-1:ℤ) * h3, by omega, by omega⟩
  exact this.1

lemma bitOne_flip (x : ℤ) (k : ℕ) : bitOne (-1 - x) k ↔ ¬ bitOne x k := by
  unfold bitOne
  rw [div_flip]
  omega

lemma epsLt_flip (ε : ℕ → Bool) (x y : ℤ) :
    epsLt ε x y ↔ epsLt (fun k => !ε k) (-1 - x) (-1 - y) := by
  unfold epsLt
  have e : (-1 - y) - (-1 - x) = x - y := by ring
  have pv : padicValInt 2 (x - y) = padicValInt 2 (y - x) := by
    rw [padicValInt, padicValInt, ← Int.natAbs_neg, neg_sub]
  rw [e, pv, bitOne_flip]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨by omega, ?_⟩; cases h : ε (padicValInt 2 (y - x)) <;> simp_all
  · rintro ⟨h1, h2⟩; refine ⟨by omega, ?_⟩; cases h : ε (padicValInt 2 (y - x)) <;> simp_all

lemma idxOf_map_inj (f : ℤ → ℤ) (hf : Function.Injective f) (x : ℤ) :
    ∀ P : List ℤ, (P.map f).idxOf (f x) = P.idxOf x := by
  intro P
  induction P with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = x
    · subst h; simp
    · have : f a ≠ f x := fun h' => h (hf h')
      simp [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ this, ih]

lemma compLt_map (R R' : ℤ → ℤ → Prop) (hR : ∀ x y, R x y ↔ R' (-1 - x) (-1 - y))
    (P : List ℤ) (x y : ℤ) :
    compLt R P x y ↔ compLt R' (P.map (fun z => -1 - z)) (-1 - x) (-1 - y) := by
  have hf : Function.Injective (fun z : ℤ => -1 - z) := fun a b h => by simp at h; omega
  have hm : ∀ z, (-1 - z) ∈ P.map (fun z => -1 - z) ↔ z ∈ P := fun z =>
    List.mem_map_of_injective hf
  have hi := fun z => idxOf_map_inj (fun z : ℤ => -1 - z) hf z P
  unfold compLt
  rw [hm, hm, hi, hi, hR]

theorem safe_map_of (R R' : ℤ → ℤ → Prop) (hR : ∀ x y, R x y ↔ R' (-1 - x) (-1 - y))
    (P : List ℤ) (h : Safe R P) : Safe R' (P.map (fun z => -1 - z)) := by
  intro a r hr hc
  have key : ∀ j : ℤ, -1 - ((-1 - a) + j * (-r)) = a + j * r := fun j => by ring
  apply h (-1 - a) (-r) (by omega)
  have c := fun (j : ℤ) => compLt_map R R' hR P ((-1 - a) + j * (-r)) ((-1 - a) + (j + 1) * (-r))
  have c0 := c 0; have c1 := c 1; have c2 := c 2
  rw [key, key] at c0 c1 c2
  norm_num at c0 c1 c2
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [c0]; convert h1 using 2
  · have := c1.2 h2; convert this using 2; ring
  · have := c2.2 h3; convert this using 2 <;> ring

/-- **Bit-flip symmetry** (Astra): under `σ(x) = -1 - x`, a list `Q` is safe for the ε-order iff
`σ(Q)` is safe for the complementary order `k ↦ !ε k`. -/
theorem epsLt_safe_flip_iff (ε : ℕ → Bool) (Q : List ℤ) :
    Safe (epsLt ε) Q ↔ Safe (epsLt (fun k => !ε k)) (Q.map (fun x => -1 - x)) := by
  constructor
  · exact safe_map_of _ _ (epsLt_flip ε) Q
  · intro h
    have h2 := safe_map_of _ _ (epsLt_flip (fun k => !ε k)) _ h
    have e1 : (Q.map (fun x : ℤ => -1 - x)).map (fun x => -1 - x) = Q := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id Q]
      apply List.map_congr_left
      intro x _; simp
    rw [e1] at h2
    simpa using h2

end E195S52



open Erdos195 in
theorem solution (ε : ℕ → Bool) (Q : List ℤ) :
    Safe (epsLt ε) Q ↔ Safe (epsLt (fun k => !ε k)) (Q.map (fun x => -1 - x)) :=
  E195S52.epsLt_safe_flip_iff ε Q
