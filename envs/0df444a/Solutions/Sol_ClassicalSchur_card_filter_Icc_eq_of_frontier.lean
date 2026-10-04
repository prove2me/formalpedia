-- Prove2me | solution 1 for ClassicalSchur.card_filter_Icc_eq_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:01.254016+00:00
-- url     : https://prove2.me/submissions/5e0f8a33-cdcd-46fe-ad76-7eb0edba6c43

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 7 file-scoped / sub-threshold helper(s)
--   rename  : card_filter_Icc_eq_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
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

/-- If `|s|` numbers, each at most `b`, sum to `|s| · b`, then each is `b`. -/
private theorem eq_of_sum_eq_card_mul {ι : Type*} {s : Finset ι} {f : ι → ℕ} {b : ℕ}
    (hle : ∀ i ∈ s, f i ≤ b) (hsum : ∑ i ∈ s, f i = s.card * b) : ∀ i ∈ s, f i = b := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ s, f j < ∑ _j ∈ s, b :=
    sum_lt_sum hle ⟨i, hi, lt_of_le_of_ne (hle i hi) hne⟩
  rw [sum_const, smul_eq_mul] at hlt
  omega

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

end ClassicalSchur

open ClassicalSchur in
theorem solution {k t m : ℕ} (hR : TriangleRamsey k (2 * t + 2))
    (hm : m = (k + 1) * t) {c : ℕ → Fin (k + 1)} (hc : SchurColoring (2 * m + 1) c)
    (j : Fin (k + 1)) : ((Icc 1 m).filter fun d => c d = j).card = t := by
  have hrange : ∀ x ∈ range (2 * m + 2), x ≤ 2 * m + 1 := fun x hx => by
    have := mem_range.mp hx
    omega
  have hle : ∀ j : Fin (k + 1), ((Icc 1 m).filter fun d => c d = j).card ≤ t := by
    intro j
    have h2 := two_mul_card_le_card_colorNbhd c m j
    have hP : (colorNbhd c (range (2 * m + 2)) m j).card < 2 * t + 2 := by
      refine hc.card_lt hR (fun x hx => hrange x (mem_colorNbhd.mp hx).2.1)
        (K := univ.erase j) (by simp) fun x hx y hy hxy => ?_
      exact mem_erase.mpr
        ⟨hc.color_ne_of_mem_colorNbhd hrange (by omega) hx hy hxy, mem_univ _⟩
    have := card_erase_le (s := colorNbhd c (range (2 * m + 2)) m j) (a := 2 * m + 1)
    omega
  have hsum : ∑ j, ((Icc 1 m).filter fun d => c d = j).card =
      (univ : Finset (Fin (k + 1))).card * t := by
    rw [← card_eq_sum_card_fiberwise fun d _ => mem_univ (c d), Nat.card_Icc, card_univ,
      Fintype.card_fin, hm]
    omega
  exact eq_of_sum_eq_card_mul (fun j _ => hle j) hsum j (mem_univ j)
