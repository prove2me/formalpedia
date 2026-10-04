-- Prove2me | solution 1 for CannonFloydParry.mem_closure_mapA_mapB_of_standardDyadicPartition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T22:49:21.567012+00:00
-- url     : https://prove2.me/submissions/1589b8cd-dc6e-4a88-994d-54bc969542e7

import Definitions.Def_CannonFloydParry
import Mathlib
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F

open CannonFloydParry

theorem solution {n : ℕ} {f : UI ≃o UI}
    (x y : Fin (n + 1) → UI)
    (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : (x 0 : ℝ) = 0) (hxn : (x (Fin.last n) : ℝ) = 1)
    (hy0 : (y 0 : ℝ) = 0) (hyn : (y (Fin.last n) : ℝ) = 1)
    (hxs : ∀ i : Fin n, ∃ a k : ℕ,
      (x i.castSucc : ℝ) = a / 2 ^ k ∧ (x i.succ : ℝ) = (a + 1) / 2 ^ k)
    (hys : ∀ i : Fin n, ∃ a k : ℕ,
      (y i.castSucc : ℝ) = a / 2 ^ k ∧ (y i.succ : ℝ) = (a + 1) / 2 ^ k)
    (hf : ∀ (i : Fin n) (z : UI), (x i.castSucc : ℝ) ≤ (z : ℝ) → (z : ℝ) ≤ (x i.succ : ℝ) →
      (f z : ℝ) =
        ((y i.succ : ℝ) - (y i.castSucc : ℝ)) / ((x i.succ : ℝ) - (x i.castSucc : ℝ))
          * ((z : ℝ) - (x i.castSucc : ℝ)) + (y i.castSucc : ℝ)) :
    f ∈ Subgroup.closure {mapA, mapB} := by
  classical
  rw [closure_mapA_mapB_eq_F]
  apply Subgroup.subset_closure
  show IsThompson f
  refine ⟨Finset.univ.image (fun i => (x i : ℝ)), ?_, ?_⟩
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    induction i using Fin.lastCases with
    | last => exact ⟨1, 0, by rw [hxn]; norm_num⟩
    | cast j =>
      obtain ⟨a, k, ha, -⟩ := hxs j
      exact ⟨a, k, by rw [ha]; push_cast; rfl⟩
  · intro p q hpq hdisj
    -- locate the partition interval containing `[p, q]`
    have hfind : ∃ i : Fin n, (x i.castSucc : ℝ) ≤ (p : ℝ) ∧ (q : ℝ) ≤ (x i.succ : ℝ) := by
      by_contra hno
      push Not at hno
      have key : ∀ m : ℕ, (hm : m ≤ n) → (x ⟨m, Nat.lt_succ_of_le hm⟩ : ℝ) ≤ (p : ℝ) := by
        intro m
        induction m with
        | zero => intro _; have : (x ⟨0, Nat.succ_pos n⟩ : ℝ) = 0 := hx0
                  rw [this]; exact p.2.1
        | succ m ih =>
          intro hm
          have hm' : m < n := hm
          have h1 := ih hm'.le
          have h2 := hno ⟨m, hm'⟩ h1
          have hs : (x (⟨m, hm'⟩ : Fin n).succ : ℝ) = (x ⟨m + 1, Nat.lt_succ_of_le hm⟩ : ℝ) := rfl
          rw [hs] at h2
          by_contra h3
          push Not at h3
          have hmem : (x ⟨m + 1, Nat.lt_succ_of_le hm⟩ : ℝ) ∈
              Set.Ioo (p : ℝ) (q : ℝ) ∩ ((Finset.univ.image (fun i => (x i : ℝ)) : Finset ℝ) : Set ℝ) :=
            ⟨⟨h3, h2⟩, by simp⟩
          rw [hdisj] at hmem
          exact hmem
      have hlast := key n le_rfl
      have : (x ⟨n, Nat.lt_succ_self n⟩ : ℝ) = 1 := hxn
      rw [this] at hlast
      have := q.2.2
      linarith
    obtain ⟨i, hpi, hqi⟩ := hfind
    obtain ⟨a, k, hxa, hxa'⟩ := hxs i
    obtain ⟨b, l, hyb, hyb'⟩ := hys i
    have hs : ((y i.succ : ℝ) - (y i.castSucc : ℝ)) / ((x i.succ : ℝ) - (x i.castSucc : ℝ))
        = (2 : ℝ) ^ ((k : ℤ) - l) := by
      rw [hxa, hxa', hyb, hyb', zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
      field_simp
      ring
    refine ⟨(k : ℤ) - l, (y i.castSucc : ℝ) - 2 ^ ((k : ℤ) - l) * (x i.castSucc : ℝ), ?_⟩
    intro z hz
    rw [hf i z (hpi.trans hz.1) (hz.2.trans hqi), hs]
    ring
