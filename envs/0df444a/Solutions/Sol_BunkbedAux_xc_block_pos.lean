-- Prove2me | solution 1 for BunkbedAux.xc_block_pos
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:17:07.141027+00:00
-- url     : https://prove2.me/submissions/9ce6b309-a91e-444b-971d-979a5f8486e4

import Theorems.Thm_BunkbedAux_xc_and_A_weight
import Theorems.Thm_BunkbedAux_A_block_value
open Bunkbed Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset SimpleGraph

private lemma wt_nonneg (P : WZ → ℚ) (hnn : ∀ s, 0 ≤ P s)
    (hW : 0 ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) : ∀ q : WZExt, 0 ≤ wt P q := by
  intro q
  rcases q with ⟨a, b⟩ | i
  · exact mul_nonneg (hnn a) (hnn b)
  · fin_cases i <;> simp only [wt]
    · exact mul_nonneg (hnn _) (hnn _)
    · exact hW
    · exact mul_nonneg (hnn _) (hnn _)
    · exact hW

private lemma Asub : (univ.filter (fun Ψ : Fin 6 → WZExt =>
      ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)))
    ⊆ univ.filter (fun Ψ : Fin 6 → WZExt =>
      ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)) := by
  intro Ψ hΨ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
  have := (Finset.mem_filter.mp hΨ).2 h
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_insert.mp this with h1 | h1
  · rw [h1]; exact ⟨by decide, by decide⟩
  · rw [Finset.mem_singleton.mp h1]; exact ⟨by decide, by decide⟩

set_option maxHeartbeats 1000000 in
theorem solution (P : WZ → ℚ)
    (hnn : ∀ s, 0 ≤ P s)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1)
    (hpos : 0 < P .abc * P .a_b_c - P .ab_c * P .ac_b)
    (h400 : 400 * P .a_bc ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) :
    0 < ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)),
        (∏ h, wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)) := by
  obtain ⟨hZ, hA⟩ := BunkbedAux.xc_and_A_weight P hsum
  have hwtnn := wt_nonneg P hnn (le_of_lt hpos)
  have hprodnn : ∀ Ψ : Fin 6 → WZExt, 0 ≤ ∏ h, wt P (Ψ h) :=
    fun Ψ => Finset.prod_nonneg (fun h _ => hwtnn _)
  -- split the complement into the all-minus block and the rest
  have hsplit := Finset.sum_sdiff (f := fun Ψ : Fin 6 → WZExt => (∏ h, wt P (Ψ h)) *
      ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
          ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
      - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
          ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))) Asub
  have hwsplit := Finset.sum_sdiff (f := fun Ψ : Fin 6 → WZExt => ∏ h, wt P (Ψ h)) Asub
  -- the error block is bounded below by minus its total weight
  have herr : -(∑ Ψ ∈ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)))
        \ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt))), ∏ h, wt P (Ψ h))
      ≤ ∑ Ψ ∈ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)))
        \ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt))),
        (∏ h, wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun Ψ _ => ?_)
    have hd : (-1 : ℚ) ≤ (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
          ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
        - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
          ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0) := by
      split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_left hd (hprodnn Ψ)
    linarith [this]
  -- arithmetic
  have hz0 : (0 : ℚ) ≤ P .a_bc := hnn _
  have hWpos : (0 : ℚ) < P .abc * P .a_b_c - P .ab_c * P .ac_b := hpos
  have hZle : 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc
      ≤ (P .abc * P .a_b_c - P .ab_c * P .ac_b) * (401 / 200) := by
    linarith [mul_self_nonneg (P WZ.a_bc), h400]
  have hZ0 : (0 : ℚ) ≤ 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc
      - P .a_bc * P .a_bc := by
    have hz1 : P WZ.a_bc ≤ 1 := by
      linarith [hnn WZ.abc, hnn WZ.a_b_c, hnn WZ.ab_c, hnn WZ.ac_b]
    have : (0 : ℚ) ≤ P WZ.a_bc * (2 - P WZ.a_bc) :=
      mul_nonneg hz0 (by linarith)
    nlinarith [this, hWpos]
  have hZ6 : (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc) ^ 6
      ≤ ((P .abc * P .a_b_c - P .ab_c * P .ac_b) * (401 / 200)) ^ 6 :=
    pow_le_pow_left₀ hZ0 hZle 6
  have hW6 : (0 : ℚ) < (P .abc * P .a_b_c - P .ab_c * P .ac_b) ^ 6 := pow_pos hWpos 6
  rw [← hsplit, BunkbedAux.A_block_value P]
  have hwe : (∑ Ψ ∈ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)))
        \ (univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt))), ∏ h, wt P (Ψ h))
      = (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc) ^ 6
        - (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b)) ^ 6 := by
    have := hwsplit
    rw [hA] at this
    rw [hZ] at this
    linarith [this]
  rw [hwe] at herr
  nlinarith [herr, hZ6, hW6]
