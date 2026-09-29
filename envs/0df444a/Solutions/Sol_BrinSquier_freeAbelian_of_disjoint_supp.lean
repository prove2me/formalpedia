-- Prove2me | solution 1 for BrinSquier.freeAbelian_of_disjoint_supp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T09:09:46.108524+00:00
-- url     : https://prove2.me/submissions/d19f946a-0382-4149-a165-4e6815773dc7

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_12

lemma zpow_fix {v : ℝ ≃o ℝ} {a : ℝ} (h : v a = a) : ∀ k : ℤ, (v ^ k) a = a := by
  have hinv : v⁻¹ a = a := v.injective (by rw [RelIso.apply_inv_self, h])
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [zpow_add v (m : ℤ) 1, zpow_one]; show (v ^ (m : ℤ)) (v a) = a; rw [h, ih]
  | pred m ih =>
      rw [show (-(m : ℤ) - 1) = (-(m : ℤ)) + (-1) by ring, zpow_add v (-(m : ℤ)) (-1),
        zpow_neg_one]
      show (v ^ (-(m : ℤ))) (v⁻¹ a) = a
      rw [hinv, ih]

/-- A point moved by `v` is carried by any power of `v` to another moved point. -/
lemma moves_zpow {v : ℝ ≃o ℝ} {a : ℝ} (ha : v a ≠ a) (k : ℤ) :
    v ((v ^ k) a) ≠ (v ^ k) a := by
  intro hcon
  apply ha
  have h1 : (v ^ (-k)) ((v ^ k) a) = a := by
    show (v ^ (-k) * v ^ k) a = a; rw [← zpow_add]; simp
  rw [zpow_fix hcon (-k)] at h1
  rw [← h1]
  exact hcon

end BS_12

open BS_12 in
theorem solution {ι : Type*} (x : ι → ℝ ≃o ℝ)
    (hinf : ∀ i, ∀ k : ℤ, k ≠ 0 → x i ^ k ≠ 1)
    (hdisj : ∀ i j, i ≠ j → ∀ a : ℝ, x i a = a ∨ x j a = a)
    (l : List ι) (hl : l.Nodup) (n : ι → ℤ)
    (hprod : (l.map (fun i => x i ^ n i)).prod = 1) :
    ∀ i ∈ l, n i = 0 := by
  intro i hi
  -- factors other than `i` fix every point that `x i` moves
  have fixes : ∀ (l' : List ι), i ∉ l' → ∀ a : ℝ, x i a ≠ a →
      (l'.map (fun j => x j ^ n j)).prod a = a := by
    intro l'
    induction l' with
    | nil => intro _ a _; rfl
    | cons j rest ih =>
        intro hni a ha
        have hji : j ≠ i := fun h => hni (by rw [← h]; exact List.mem_cons_self)
        have hnr : i ∉ rest := fun h => hni (List.mem_cons_of_mem _ h)
        simp only [List.map_cons, List.prod_cons]
        show (x j ^ n j) ((rest.map (fun k => x k ^ n k)).prod a) = a
        rw [ih hnr a ha]
        rcases hdisj i j (Ne.symm hji) a with h1 | h2
        · exact absurd h1 ha
        · exact zpow_fix h2 (n j)
  -- so on those points the whole product acts as `x i ^ n i`
  have acts : ∀ (l' : List ι), l'.Nodup → i ∈ l' → ∀ a : ℝ, x i a ≠ a →
      (l'.map (fun j => x j ^ n j)).prod a = (x i ^ n i) a := by
    intro l'
    induction l' with
    | nil => intro _ h; exact absurd h (by simp)
    | cons j rest ih =>
        intro hnd hmem a ha
        obtain ⟨hjr, hndr⟩ := List.nodup_cons.mp hnd
        simp only [List.map_cons, List.prod_cons]
        show (x j ^ n j) ((rest.map (fun k => x k ^ n k)).prod a) = (x i ^ n i) a
        rcases List.mem_cons.mp hmem with hij | hir
        · rw [← hij, fixes rest (by rw [← hij] at hjr; exact hjr) a ha]
        · have hji : j ≠ i := fun h => hjr (by rw [h]; exact hir)
          rw [ih hndr hir a ha]
          rcases hdisj i j (Ne.symm hji) ((x i ^ n i) a) with h1 | h2
          · exact absurd h1 (moves_zpow ha (n i))
          · exact zpow_fix h2 (n j)
  -- hence `x i ^ n i` is the identity, so its exponent vanishes
  have hid : x i ^ n i = 1 := by
    apply RelIso.ext
    intro a
    show (x i ^ n i) a = a
    by_cases ha : x i a = a
    · exact zpow_fix ha (n i)
    · have h2 := acts l hl hi a ha
      rw [hprod] at h2
      exact h2.symm
  by_contra hne
  exact hinf i (n i) hne hid
