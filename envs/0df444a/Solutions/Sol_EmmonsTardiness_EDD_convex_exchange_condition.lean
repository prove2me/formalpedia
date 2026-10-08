-- Prove2me | solution 1 for EmmonsTardiness.EDD.convex_exchange_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:28:59.641166+00:00
-- url     : https://prove2.me/submissions/047c0e23-30e4-4486-8e6a-2ff6d011d057

import Mathlib

set_option autoImplicit false

lemma emmons_cvx_aux (g : ℝ → ℝ) (hg : ConvexOn ℝ (Set.Ici 0) g)
    (a b d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hdl : d ≤ b - a) :
    g (a + d) + g (b - d) ≤ g a + g b := by
  rcases eq_or_lt_of_le hd with h0 | hpos
  · subst h0; simp
  have hL : 0 < b - a := lt_of_lt_of_le hpos hdl
  have hb : (0:ℝ) ≤ b := by linarith
  have hLne : b - a ≠ 0 := hL.ne'
  have hw1 : 0 ≤ (b - a - d) / (b - a) := div_nonneg (by linarith) hL.le
  have hw2 : 0 ≤ d / (b - a) := div_nonneg hd hL.le
  have hsum : (b - a - d) / (b - a) + d / (b - a) = 1 := by field_simp; ring
  have hsum' : d / (b - a) + (b - a - d) / (b - a) = 1 := by linarith
  have e1 : ((b - a - d) / (b - a)) • a + (d / (b - a)) • b = a + d := by
    simp only [smul_eq_mul]; field_simp; ring
  have e2 : (d / (b - a)) • a + ((b - a - d) / (b - a)) • b = b - d := by
    simp only [smul_eq_mul]; field_simp; ring
  have i1 := hg.2 (show a ∈ Set.Ici (0:ℝ) from ha) (show b ∈ Set.Ici (0:ℝ) from hb) hw1 hw2 hsum
  have i2 := hg.2 (show a ∈ Set.Ici (0:ℝ) from ha) (show b ∈ Set.Ici (0:ℝ) from hb) hw2 hw1 hsum'
  rw [e1] at i1; rw [e2] at i2
  simp only [smul_eq_mul] at i1 i2
  have h3 : (b - a - d) / (b - a) * g a + d / (b - a) * g a = g a := by
    rw [← add_mul, hsum, one_mul]
  have h4 : d / (b - a) * g b + (b - a - d) / (b - a) * g b = g b := by
    rw [← add_mul, hsum', one_mul]
  linarith

theorem solution (g : ℝ → ℝ)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (Tjb Tja Tkb Tka : ℝ)
    (hTja : 0 ≤ Tja) (hj : Tja ≤ Tjb) (hTkb : 0 ≤ Tkb) (hk : Tkb ≤ Tka)
    (h1 : Tka - Tkb ≤ Tjb - Tja) (h2 : Tka ≤ Tjb) :
    g Tka - g Tkb ≤ g Tjb - g Tja := by
  have key := emmons_cvx_aux g hg Tkb Tjb (Tka - Tkb) hTkb (by linarith) (by linarith)
  have hm : g Tja ≤ g (Tjb - (Tka - Tkb)) :=
    hgm (show Tja ∈ Set.Ici (0:ℝ) from hTja) (show Tjb - (Tka - Tkb) ∈ Set.Ici (0:ℝ) by
      simp only [Set.mem_Ici]; linarith) (by linarith)
  have : Tkb + (Tka - Tkb) = Tka := by ring
  rw [this] at key
  linarith
