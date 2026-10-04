-- Prove2me | solution 1 for ClassicalSchur.card_centralNbhd_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:01.742358+00:00
-- url     : https://prove2.me/submissions/c1138531-d7f5-439a-884e-ca4b67dec792

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 10 file-scoped / sub-threshold helper(s)
--   rename  : card_centralNbhd_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_card_filter_Icc_eq_of_frontier
import Theorems.Thm_ClassicalSchur_triangleRamsey_succ
import Mathlib

open Finset

namespace ClassicalSchur

/-- Membership in a colour neighbourhood. -/
theorem mem_colorNbhd {n : ℕ} {c : ℕ → Fin n} {V : Finset ℕ} {v w : ℕ} {i : Fin n} :
    w ∈ colorNbhd c V v i ↔ w ≠ v ∧ w ∈ V ∧ c (Nat.dist v w) = i := by
  simp [colorNbhd, and_assoc]

/-- The points `m ± d` for `d ∈ [1, m]` with `c d = j` lie in the colour-`j`
neighbourhood of the centre `m` of `[0, 2m + 1]`, and are not the endpoint. -/
private theorem two_mul_card_le_card_colorNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (j : Fin n) :
    2 * ((Icc 1 m).filter fun d => c d = j).card ≤
      ((colorNbhd c (range (2 * m + 2)) m j).erase (2 * m + 1)).card := by
  set D := (Icc 1 m).filter fun d => c d = j with hD
  have hDm : ∀ d ∈ D, 1 ≤ d ∧ d ≤ m ∧ c d = j := by
    intro d hd
    obtain ⟨h1, h2⟩ := mem_filter.mp hd
    exact ⟨(mem_Icc.mp h1).1, (mem_Icc.mp h1).2, h2⟩
  have hsub : D.image (fun d => m - d) ∪ D.image (fun d => m + d) ⊆
      (colorNbhd c (range (2 * m + 2)) m j).erase (2 * m + 1) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hDm d hd
      refine mem_erase.mpr ⟨by omega, mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩⟩
      rwa [show Nat.dist m (m - d) = d by unfold Nat.dist; omega]
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hDm d hd
      refine mem_erase.mpr ⟨by omega, mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩⟩
      rwa [show Nat.dist m (m + d) = d by unfold Nat.dist; omega]
  have hinj1 : Set.InjOn (fun d => m - d) D := by
    intro a ha b hb hab
    have := hDm a ha
    have := hDm b hb
    simp only at hab
    omega
  have hinj2 : Set.InjOn (fun d => m + d) D := by
    intro a _ b _ hab
    simp only at hab
    omega
  have hdisj : Disjoint (D.image fun d => m - d) (D.image fun d => m + d) := by
    rw [disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx1
    obtain ⟨b, hb, hab⟩ := mem_image.mp hx2
    have := hDm a ha
    have := hDm b hb
    omega
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj1, card_image_of_injOn hinj2] at this
  omega

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

/-- `k + 1` colours force a monochromatic triangle on `(k + 1)u + 2` points
when `k` colours force one on `u + 1` points. -/
private theorem triangleRamsey_of_two_mul {k u t : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) : TriangleRamsey (k + 1) (2 * t + 2) := by
  have h := triangleRamsey_succ hR
  rwa [Nat.add_sub_cancel, ← h2t] at h

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

/-- If the differences of the points of `V ⊆ [0, N]` take their colours in a
set `K` of at most `k` colours, and `k` colours force a monochromatic triangle
on `r` points, then `V` has fewer than `r` points. -/
theorem SchurColoring.card_lt {n N k r : ℕ} {c : ℕ → Fin n} (hc : SchurColoring N c)
    (hR : TriangleRamsey k r) {V : Finset ℕ} (hV : ∀ x ∈ V, x ≤ N) {K : Finset (Fin n)}
    (hK : K.card ≤ k) (hcol : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → c (Nat.dist x y) ∈ K) :
    V.card < r := by
  by_contra hr
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, e1, e2⟩ :=
    hR V (K.image Fin.val) (fun x y => (c (Nat.dist x y) : ℕ)) (card_image_le.trans hK)
      (not_lt.mp hr) (fun x hx y hy hxy => mem_image_of_mem _ (hcol x hx y hy hxy.ne))
  exact hc.not_mono (hV x hx) (hV y hy) (hV z hz) hxy.ne (by omega) hyz.ne (Fin.ext e2)
    ((Fin.ext e2).symm.trans (Fin.ext e1))

end ClassicalSchur

open ClassicalSchur in
theorem solution {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : (centralNbhd c m).card = 2 * t + 1 := by
  have hR' := triangleRamsey_of_two_mul hR h2t
  have hD : ((Icc 1 m).filter fun d => c d = c (m + 1)).card = t :=
    card_filter_Icc_eq_of_frontier hR' (by rw [hm]) hc (c (m + 1))
  have h2 := two_mul_card_le_card_colorNbhd c m (c (m + 1))
  have hN := card_erase_add_one (endpoint_mem_centralNbhd c m)
  have hlt : (centralNbhd c m).card < 2 * t + 2 := by
    refine hc.card_lt hR' (fun x hx => (mem_centralNbhd.mp hx).2.1) (K := univ.erase (c (m + 1)))
      (by simp) fun x hx y hy hxy => ?_
    exact mem_erase.mpr ⟨hc.color_ne_of_mem_centralNbhd hx hy hxy, mem_univ _⟩
  unfold centralNbhd at hN hlt ⊢
  omega
