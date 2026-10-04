-- Prove2me | solution 1 for ClassicalSchur.color_reflect_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:03.942781+00:00
-- url     : https://prove2.me/submissions/33c50a16-0669-4e12-88aa-6d54aef9cdf4

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 8 file-scoped / sub-threshold helper(s)
--   rename  : color_reflect_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_card_colorNbhd_centralNbhd_of_frontier
import Theorems.Thm_ClassicalSchur_color_eq_of_card_filter_eq
import Mathlib

open Finset

namespace ClassicalSchur

/-- Membership in a colour neighbourhood. -/
theorem mem_colorNbhd {n : ℕ} {c : ℕ → Fin n} {V : Finset ℕ} {v w : ℕ} {i : Fin n} :
    w ∈ colorNbhd c V v i ↔ w ≠ v ∧ w ∈ V ∧ c (Nat.dist v w) = i := by
  simp [colorNbhd, and_assoc]

/-- Membership in the central neighbourhood: `x ∈ [0, 2m + 1]`, `x ≠ m`, and
`c |m − x| = c (m + 1)`. -/
theorem mem_centralNbhd {n : ℕ} {c : ℕ → Fin n} {m x : ℕ} :
    x ∈ centralNbhd c m ↔ x ≠ m ∧ x ≤ 2 * m + 1 ∧ c (Nat.dist m x) = c (m + 1) := by
  rw [centralNbhd, mem_colorNbhd, mem_range, Nat.lt_succ_iff]

/-- The endpoint `2m + 1` is in the central neighbourhood, since
`(2m + 1) − m = m + 1`. -/
theorem endpoint_mem_centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) :
    2 * m + 1 ∈ centralNbhd c m :=
  mem_centralNbhd.mpr ⟨by omega, le_rfl, by rw [show Nat.dist m (2 * m + 1) = m + 1 by
    unfold Nat.dist; omega]⟩

/-- Of three points on a line, one distance is the sum of the other two. -/
private theorem dist_cases (a b w : ℕ) :
    Nat.dist a b + Nat.dist b w = Nat.dist a w ∨
    Nat.dist a b + Nat.dist a w = Nat.dist b w ∨
    Nat.dist a w + Nat.dist b w = Nat.dist a b := by
  unfold Nat.dist
  omega

/-- The difference colouring of a Schur colouring of `[1, N]` has no
monochromatic triangle on three distinct points of `[0, N]`. -/
theorem SchurColoring.not_mono {n N : ℕ} {c : ℕ → Fin n} (hc : SchurColoring N c)
    {a b w : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hw : w ≤ N) (hab : a ≠ b) (haw : a ≠ w)
    (hbw : b ≠ w) (h1 : c (Nat.dist a b) = c (Nat.dist a w))
    (h2 : c (Nat.dist a w) = c (Nat.dist b w)) : False := by
  have pab := Nat.dist_pos_of_ne hab
  have paw := Nat.dist_pos_of_ne haw
  have pbw := Nat.dist_pos_of_ne hbw
  have lab : Nat.dist a b ≤ N := by unfold Nat.dist; omega
  have law : Nat.dist a w ≤ N := by unfold Nat.dist; omega
  have lbw : Nat.dist b w ≤ N := by unfold Nat.dist; omega
  rcases dist_cases a b w with h | h | h
  · exact hc _ _ pab pbw (by omega) (h1.trans h2) (by rw [h]; exact h1.symm)
  · exact hc _ _ pab paw (by omega) h1 (by rw [h]; exact (h1.trans h2).symm)
  · exact hc _ _ paw pbw (by omega) h2 (by rw [h]; exact h1)

/-- Two points of a colour-`i` neighbourhood are not joined in colour `i`. -/
theorem SchurColoring.color_ne_of_mem_colorNbhd {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) {V : Finset ℕ} (hV : ∀ x ∈ V, x ≤ N) {v : ℕ} (hv : v ≤ N)
    {i : Fin n} {x y : ℕ} (hx : x ∈ colorNbhd c V v i) (hy : y ∈ colorNbhd c V v i)
    (hxy : x ≠ y) : c (Nat.dist x y) ≠ i := by
  intro h
  obtain ⟨hxv, hxV, hxi⟩ := mem_colorNbhd.mp hx
  obtain ⟨hyv, hyV, hyi⟩ := mem_colorNbhd.mp hy
  exact hc.not_mono hv (hV x hxV) (hV y hyV) (Ne.symm hxv) (Ne.symm hyv) hxy
    (hxi.trans hyi.symm) (hyi.trans h.symm)

/-- No two points of the central neighbourhood are joined in its colour. -/
theorem SchurColoring.color_ne_of_mem_centralNbhd {n m : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring (2 * m + 1) c) {x y : ℕ} (hx : x ∈ centralNbhd c m)
    (hy : y ∈ centralNbhd c m) (hxy : x ≠ y) : c (Nat.dist x y) ≠ c (m + 1) :=
  hc.color_ne_of_mem_colorNbhd (fun z hz => Nat.lt_succ_iff.mp (mem_range.mp hz)) (by omega)
    hx hy hxy

/-- The reflection `x ↦ 2m − x` maps the central neighbourhood without its
endpoint to itself. -/
theorem reflect_mem_centralNbhd {n : ℕ} {c : ℕ → Fin n} {m x : ℕ}
    (hx : x ∈ centralNbhd c m) (hxN : x ≠ 2 * m + 1) :
    2 * m - x ∈ centralNbhd c m ∧ 2 * m - x ≠ 2 * m + 1 := by
  obtain ⟨hxm, hxle, hxq⟩ := mem_centralNbhd.mp hx
  refine ⟨mem_centralNbhd.mpr ⟨by omega, by omega, ?_⟩, by omega⟩
  rwa [show Nat.dist m (2 * m - x) = Nat.dist m x by unfold Nat.dist; omega]

end ClassicalSchur

open ClassicalSchur in
theorem solution {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {d : ℕ} (hd : 0 < d) (hdm : d ≤ m)
    (hq : c d = c (m + 1)) : c (m + 1 - d) = c (m + 1 + d) := by
  set V := centralNbhd c m with hV
  set N := 2 * m + 1 with hN
  have hNV : N ∈ V := endpoint_mem_centralNbhd c m
  have hVN : ∀ x ∈ V, x ≤ N := fun x hx => (mem_centralNbhd.mp hx).2.1
  have hmdV : m + d ∈ V.erase N := by
    refine mem_erase.mpr ⟨by omega, mem_centralNbhd.mpr ⟨by omega, by omega, ?_⟩⟩
    rwa [show Nat.dist m (m + d) = d by unfold Nat.dist; omega]
  have hmem : ∀ x ∈ V.erase N, x ∈ V ∧ x ≤ 2 * m := fun x hx =>
    ⟨mem_of_mem_erase hx, by have := hVN x (mem_of_mem_erase hx); have := ne_of_mem_erase hx; omega⟩
  have key := color_eq_of_card_filter_eq (fun x y => c (Nat.dist x y)) (W := V.erase N) (e := N)
    (notMem_erase N V) (fun x => 2 * m - x)
    (fun x hx => by
      obtain ⟨h1, h2⟩ := reflect_mem_centralNbhd (mem_of_mem_erase hx) (ne_of_mem_erase hx)
      exact mem_erase.mpr ⟨h2, h1⟩)
    (fun x hx => by have := (hmem x hx).2; omega)
    (fun x hx y hy => by
      have := (hmem x hx).2
      have := (hmem y hy).2
      rw [show Nat.dist (2 * m - x) (2 * m - y) = Nat.dist x y by unfold Nat.dist; omega])
    hmdV (fun i => by
      rw [insert_erase hNV]
      have hv1 : m + d ∈ V := mem_of_mem_erase hmdV
      have hv2 : 2 * m - (m + d) ∈ V :=
        (reflect_mem_centralNbhd hv1 (ne_of_mem_erase hmdV)).1
      change (colorNbhd c V (m + d) i).card = (colorNbhd c V (2 * m - (m + d)) i).card
      by_cases hi : i = c (m + 1)
      · have hz : ∀ v ∈ V, (colorNbhd c V v i).card = 0 := by
          intro v hv
          rw [card_eq_zero, eq_empty_iff_forall_notMem]
          intro w hw
          obtain ⟨hwv, hwV, hwi⟩ := mem_colorNbhd.mp hw
          exact hc.color_ne_of_mem_centralNbhd hv hwV (Ne.symm hwv) (hwi.trans hi)
        rw [hz _ hv1, hz _ hv2]
      · rw [card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hv1 hi,
          card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hv2 hi])
  rwa [show Nat.dist (m + d) N = m + 1 - d by unfold Nat.dist; omega,
    show Nat.dist (2 * m - (m + d)) N = m + 1 + d by unfold Nat.dist; omega] at key
