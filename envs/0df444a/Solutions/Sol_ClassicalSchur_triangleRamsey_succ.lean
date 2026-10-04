-- Prove2me | solution 1 for ClassicalSchur.triangleRamsey_succ
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:00.201825+00:00
-- url     : https://prove2.me/submissions/4b96030d-36a0-4bd4-84e1-8b35cb3792fa

-- Generated from lean/ClassicalSchur/SchurBound.lean
--   imports : 0 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : triangleRamsey_succ -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurRamsey
import Mathlib



open ClassicalSchur in
theorem solution {k N : ℕ} (hR : TriangleRamsey k N) :
    TriangleRamsey (k + 1) ((k + 1) * (N - 1) + 2) := by
  intro V K c hK hV hc
  have hVne : V.Nonempty := by rw [← Finset.card_pos]; omega
  set v := V.min' hVne with hv
  have hvV : v ∈ V := V.min'_mem hVne
  set W := V.erase v with hW
  have hWcard : (k + 1) * (N - 1) + 1 ≤ W.card := by
    rw [hW, Finset.card_erase_of_mem hvV]
    omega
  have hvW : ∀ w ∈ W, v < w := fun w hw =>
    lt_of_le_of_ne (V.min'_le w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw).symm
  have hmaps : ∀ w ∈ W, c v w ∈ K := fun w hw =>
    hc v hvV w (Finset.mem_of_mem_erase hw) (hvW w hw)
  have hlt : K.card * (N - 1) < W.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hK) (by omega)
  obtain ⟨i, hiK, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set U := W.filter fun w => c v w = i with hU
  have hUV : U ⊆ V := fun u hu => Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1
  by_cases hmono : ∃ x ∈ U, ∃ y ∈ U, x < y ∧ c x y = i
  · obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := hmono
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact ⟨v, hvV, x, hUV hx, y, hUV hy, hvW x hx'.1, hxy, by rw [hx'.2, hcxy],
      by rw [hx'.2, hy'.2]⟩
  · push Not at hmono
    obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4⟩ := hR U (K.erase i) c
      (by rw [Finset.card_erase_of_mem hiK]; omega) (by omega)
      (fun x hx y hy hxy =>
        Finset.mem_erase.mpr ⟨hmono x hx y hy hxy, hc x (hUV hx) y (hUV hy) hxy⟩)
    exact ⟨x, hUV hx, y, hUV hy, z, hUV hz, h1, h2, h3, h4⟩
