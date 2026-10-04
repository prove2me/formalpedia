-- Prove2me | solution 1 for ClassicalSchur.endpointNbhd_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:04.543859+00:00
-- url     : https://prove2.me/submissions/413ba6f6-6463-499f-9196-3dba878cea9d

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 8 file-scoped / sub-threshold helper(s)
--   rename  : endpointNbhd_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_card_colorNbhd_centralNbhd_of_frontier
import Theorems.Thm_ClassicalSchur_color_reflect_of_frontier
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

/-- The endpoint `2m + 1` is in the central neighbourhood, since
`(2m + 1) − m = m + 1`. -/
theorem endpoint_mem_centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) :
    2 * m + 1 ∈ centralNbhd c m :=
  mem_centralNbhd.mpr ⟨by omega, le_rfl, by rw [show Nat.dist m (2 * m + 1) = m + 1 by
    unfold Nat.dist; omega]⟩

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
    (hc : SchurColoring (2 * m + 1) c) {i : Fin (k + 2)} (hi : i ≠ c (m + 1)) :
    (endpointNbhd c m i).card = u ∧
      (∀ x ∈ endpointNbhd c m i, 2 * m - x ∈ endpointNbhd c m i ∧ 2 * m - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c m i, ∀ y ∈ endpointNbhd c m i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c (m + 1) := by
  have hNV := endpoint_mem_centralNbhd c m
  refine ⟨card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hNV hi, fun x hx => ?_,
    fun x hx y hy hxy => ⟨?_, ?_⟩⟩
  · obtain ⟨hxN, hxV, hxi⟩ := mem_colorNbhd.mp hx
    obtain ⟨hxm, hxle, hxq⟩ := mem_centralNbhd.mp hxV
    obtain ⟨hJV, hJN⟩ := reflect_mem_centralNbhd hxV hxN
    refine ⟨mem_colorNbhd.mpr ⟨hJN, hJV, ?_⟩, by omega⟩
    have hd : c (Nat.dist m x) = c (m + 1) := hxq
    have key := color_reflect_of_frontier hR h2t hm hc (d := Nat.dist m x)
      (Nat.dist_pos_of_ne (Ne.symm hxm)) (by unfold Nat.dist; omega) hd
    rcases le_or_gt x m with hle | hlt
    · rw [show Nat.dist m x = m - x by unfold Nat.dist; omega] at key
      rw [show Nat.dist (2 * m + 1) x = m + 1 + (m - x) by unfold Nat.dist; omega] at hxi
      rw [show Nat.dist (2 * m + 1) (2 * m - x) = m + 1 - (m - x) by unfold Nat.dist; omega,
        key, hxi]
    · rw [show Nat.dist m x = x - m by unfold Nat.dist; omega] at key
      rw [show Nat.dist (2 * m + 1) x = m + 1 - (x - m) by unfold Nat.dist; omega] at hxi
      rw [show Nat.dist (2 * m + 1) (2 * m - x) = m + 1 + (x - m) by unfold Nat.dist; omega,
        ← key, hxi]
  · exact hc.color_ne_of_mem_colorNbhd (fun z hz => (mem_centralNbhd.mp hz).2.1) le_rfl hx hy hxy
  · exact hc.color_ne_of_mem_centralNbhd (mem_colorNbhd.mp hx).2.1 (mem_colorNbhd.mp hy).2.1 hxy
