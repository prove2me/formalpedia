-- Prove2me | solution 1 for ConstrSOSP.proposition_5_3_colour_gaps
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:53:33.945075+00:00
-- url     : https://prove2.me/submissions/6ef0d765-c095-48f0-9fe4-3e42c19cd42f

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_Colour
import Definitions.Def_ConstrSOSP_colourPhi

open ConstrSOSP in
theorem solution (n : ℕ) (hN : 10 ^ 40 ≤ gridN n)
    (aB bB aM bM aR bR aG bG : ℕ) (haB : aB ≤ gridN n) (hbB : bB ≤ gridN n)
    (haM : aM ≤ gridN n) (hbM : bM ≤ gridN n) (haR : aR ≤ gridN n) (hbR : bR ≤ gridN n)
    (haG : aG ≤ gridN n) (hbG : bG ≤ gridN n) :
    let N : ℝ := gridN n
    let B := colourPhi N Colour.blue aB bB
    let M := colourPhi N Colour.black aM bM
    let R := colourPhi N Colour.red aR bR
    let G := colourPhi N Colour.green aG bG
    10 ^ 40 ≤ R - M ∧ 10 ^ 40 ≤ G - R ∧
      10 ^ 9 < B ∧ 9995 * B ≤ R - B ∧ R - B ≤ 10000 * B ∧ 99 * B ≤ M - B ∧ M - B ≤ 101 * B ∧
      10 ^ 20 ≤ R - M ∧ 10 ^ 20 ≤ R - B := by
  have e1 : (10 : ℝ) ^ 40 ≤ (gridN n : ℝ) := by exact_mod_cast hN
  have h1 : (aB : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast haB
  have h2 : (bB : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast hbB
  have h3 : (aM : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast haM
  have h4 : (bM : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast hbM
  have h5 : (aR : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast haR
  have h6 : (bR : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast hbR
  have h7 : (aG : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast haG
  have h8 : (bG : ℝ) ≤ (gridN n : ℝ) := by exact_mod_cast hbG
  intro N B M R G
  have eN : N = (gridN n : ℝ) := rfl
  have p1 : (0 : ℝ) ≤ aB := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ bB := Nat.cast_nonneg _
  have p3 : (0 : ℝ) ≤ aM := Nat.cast_nonneg _
  have p4 : (0 : ℝ) ≤ bM := Nat.cast_nonneg _
  have p5 : (0 : ℝ) ≤ aR := Nat.cast_nonneg _
  have p6 : (0 : ℝ) ≤ bR := Nat.cast_nonneg _
  have p7 : (0 : ℝ) ≤ aG := Nat.cast_nonneg _
  have p8 : (0 : ℝ) ≤ bG := Nat.cast_nonneg _
  have eB : B = 10 ^ 4 * N - aB - bB := rfl
  have eM : M = (10 ^ 6 + 1) * N + aM - bM := rfl
  have eR : R = 10 ^ 4 * (10 ^ 4 - 2) * N - aR + bR := rfl
  have eG : G = 10 ^ 15 * N + aG - bG := rfl
  clear_value N B M R G
  subst eB eM eR eG
  rw [← eN] at e1 h1 h2 h3 h4 h5 h6 h7 h8
  norm_num at e1 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
