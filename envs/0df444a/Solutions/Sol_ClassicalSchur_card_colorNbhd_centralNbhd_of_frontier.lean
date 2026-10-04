-- Prove2me | solution 1 for ClassicalSchur.card_colorNbhd_centralNbhd_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:02.507288+00:00
-- url     : https://prove2.me/submissions/af729b4e-6451-4133-88ad-f66e0b61f37a

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 9 file-scoped / sub-threshold helper(s)
--   rename  : card_colorNbhd_centralNbhd_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_card_centralNbhd_of_frontier
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

/-- No two points of the central neighbourhood are joined in its colour. -/
theorem SchurColoring.color_ne_of_mem_centralNbhd {n m : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring (2 * m + 1) c) {x y : ℕ} (hx : x ∈ centralNbhd c m)
    (hy : y ∈ centralNbhd c m) (hxy : x ≠ y) : c (Nat.dist x y) ≠ c (m + 1) :=
  hc.color_ne_of_mem_colorNbhd (fun z hz => Nat.lt_succ_iff.mp (mem_range.mp hz)) (by omega)
    hx hy hxy

/-- If `|s|` numbers, each at most `b`, sum to `|s| · b`, then each is `b`. -/
private theorem eq_of_sum_eq_card_mul {ι : Type*} {s : Finset ι} {f : ι → ℕ} {b : ℕ}
    (hle : ∀ i ∈ s, f i ≤ b) (hsum : ∑ i ∈ s, f i = s.card * b) : ∀ i ∈ s, f i = b := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ s, f j < ∑ _j ∈ s, b :=
    sum_lt_sum hle ⟨i, hi, lt_of_le_of_ne (hle i hi) hne⟩
  rw [sum_const, smul_eq_mul] at hlt
  omega

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

/-- The degrees of `v` in the colours sum to the number of other points of `V`. -/
theorem sum_card_colorNbhd {n : ℕ} (c : ℕ → Fin n) (V : Finset ℕ) (v : ℕ) :
    ∑ i, (colorNbhd c V v i).card = (V.erase v).card :=
  (card_eq_sum_card_fiberwise fun w _ => mem_univ (c (Nat.dist v w))).symm

end ClassicalSchur

open ClassicalSchur in
theorem solution {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {v : ℕ} (hv : v ∈ centralNbhd c m) {i : Fin (k + 2)}
    (hi : i ≠ c (m + 1)) : (colorNbhd c (centralNbhd c m) v i).card = u := by
  set V := centralNbhd c m with hV
  set q := c (m + 1) with hq
  have hVN : ∀ x ∈ V, x ≤ 2 * m + 1 := fun x hx => (mem_centralNbhd.mp hx).2.1
  have hvN := hVN v hv
  -- each degree of colour `≠ q` is at most `u`
  have hle : ∀ j ∈ univ.erase q, (colorNbhd c V v j).card ≤ u := by
    intro j hj
    have hjq : j ≠ q := ne_of_mem_erase hj
    have hlt : (colorNbhd c V v j).card < u + 1 := by
      refine hc.card_lt hR (fun x hx => hVN x (mem_colorNbhd.mp hx).2.1)
        (K := (univ.erase j).erase q) ?_ fun x hx y hy hxy => ?_
      · rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hjq, mem_univ _⟩),
          card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        omega
      · refine mem_erase.mpr ⟨hc.color_ne_of_mem_centralNbhd (mem_colorNbhd.mp hx).2.1
          (mem_colorNbhd.mp hy).2.1 hxy, mem_erase.mpr ⟨?_, mem_univ _⟩⟩
        exact hc.color_ne_of_mem_colorNbhd hVN hvN hx hy hxy
    omega
  -- the degree of colour `q` is `0`
  have hzero : (colorNbhd c V v q).card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwv, hwV, hwq⟩ := mem_colorNbhd.mp hw
    exact hc.color_ne_of_mem_centralNbhd hv hwV (Ne.symm hwv) hwq
  -- the degrees sum to `2t = (k + 1)u`
  have hcard := card_centralNbhd_of_frontier hR h2t hm hc
  have hsum : ∑ j ∈ univ.erase q, (colorNbhd c V v j).card = (univ.erase q).card * u := by
    rw [sum_erase (f := fun j => (colorNbhd c V v j).card) univ hzero, sum_card_colorNbhd,
      card_erase_of_mem hv, hV, hcard,
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    rw [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, h2t]
  exact eq_of_sum_eq_card_mul hle hsum i (mem_erase.mpr ⟨hi, mem_univ _⟩)
