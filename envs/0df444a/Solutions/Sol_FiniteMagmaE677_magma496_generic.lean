-- Prove2me | solution 1 for FiniteMagmaE677.magma496_generic
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:22:00.540014+00:00
-- url     : https://prove2.me/submissions/a3c56b2e-ccef-45ee-94c1-41c5dcf2515a

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_FiniteMagmaE677
import Definitions.Def_FiniteMagmaE677_magma496

/-!
# The 496-element magma satisfies E677 and is not right-cancellative (generic form)

Let `M` be any commutative ring of characteristic two containing elements `z, w`
with `z^4+z^3+z^2+z+1 = 0` (primitive fifth root of unity) and `w^2+w+1 = 0`
(primitive cube root of unity), with `0 != 1`. Then `magma496 z w` on
`ZMod 31 x M` — the blueprint construction: base operation `3x - 2y` on
`ZMod 31`, fiber selected by the quadratic character (Euler criterion
`z ^ 15`) of the coordinate difference — satisfies E677, and it is not
right-cancellative.

The four fiber selections inside the E677 identity at `((x,s),(y,t))` are
governed by the differences `x-y`, `-2(y-x)`, `7(y-x)`, `-15(y-x)`. Since
`2^15 = 7^15 = 1` and `15^15 = -1` in `ZMod 31`, nodes 1-2 carry the
character `-(y-x)^15` and nodes 3-4 carry `+(y-x)^15`. Fermat gives the
trichotomy, and the three cases reduce to three fiber identities, each a
`linear_combination` of the cyclotomic relations and `1+1 = 0`.
-/

universe u v

theorem FiniteMagmaE677.magma496_generic {M : Type v} [CommRing M] (ζ ω : M)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hω : ω ^ 2 + ω + 1 = 0)
    (h2 : (1 : M) + 1 = 0) (h01 : (0 : M) ≠ 1) :
    FiniteMagmaE677.E677 (FiniteMagmaE677.magma496 ζ ω) ∧
    ∃ a b c : ZMod 31 × M,
      FiniteMagmaE677.magma496 ζ ω a c = FiniteMagmaE677.magma496 ζ ω b c ∧ a ≠ b := by
  have h7_15 : ((7 : ZMod 31)) ^ 15 = 1 := by decide
  have h31z : (31 : ZMod 31) = 0 := by decide
  have hneg1 : ((-1 : ZMod 31)) ^ 15 = -1 := by decide
  have hneg1ne : ((-1 : ZMod 31)) ≠ 1 := by decide
  have hn2p : ((-2 : ZMod 31)) ^ 15 = -1 := by decide
  have hn15p : ((-15 : ZMod 31)) ^ 15 = 1 := by decide
  -- Fermat trichotomy and unit cancellations, all by pure computation (no Field instance needed)
  have hfermat : ∀ d : ZMod 31, d = 0 ∨ d ^ 15 = 1 ∨ d ^ 15 = -1 := by decide
  have hu1 : ∀ u : ZMod 31, ((-1 : ZMod 31)) * u = 0 → u = 0 := by decide
  have hu2 : ∀ u : ZMod 31, ((-2 : ZMod 31)) * u = 0 → u = 0 := by decide
  have hu7 : ∀ u : ZMod 31, ((7 : ZMod 31)) * u = 0 → u = 0 := by decide
  have hu15 : ∀ u : ZMod 31, ((-15 : ZMod 31)) * u = 0 → u = 0 := by decide
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩
    have hG : (3 : ZMod 31) * y - 2 * (3 * x - 2 * (3 * (3 * y - 2 * x) - 2 * y)) = x := by
      linear_combination (y - x) * h31z
    refine Prod.ext ?_ ?_
    · simp only [FiniteMagmaE677.magma496]
      exact hG.symm
    · simp only [FiniteMagmaE677.magma496]
      rcases eq_or_ne (y - x) 0 with hd0 | hd0
      · -- diagonal: all four node differences vanish
        have e1 : FiniteMagmaE677.fiber496 ζ ω y x t s = (1 + ζ) * t + ζ * s := by
          simp [FiniteMagmaE677.fiber496,
            show x - y = 0 by rw [show x - y = -(y - x) from by ring, hd0]; ring]
        have e2 : FiniteMagmaE677.fiber496 ζ ω ((3 : ZMod 31) * y - 2 * x) y
            ((1 + ζ) * t + ζ * s) t = (1 + ζ) * ((1 + ζ) * t + ζ * s) + ζ * t := by
          simp [FiniteMagmaE677.fiber496,
            show y - ((3 : ZMod 31) * y - 2 * x) = 0 by
              rw [show y - ((3 : ZMod 31) * y - 2 * x) = (-2 : ZMod 31) * (y - x) from by ring,
                hd0]
              ring]
        have e3 : FiniteMagmaE677.fiber496 ζ ω x ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y) s ((1 + ζ) * ((1 + ζ) * t + ζ * s) + ζ * t)
            = (1 + ζ) * s + ζ * ((1 + ζ) * ((1 + ζ) * t + ζ * s) + ζ * t) := by
          simp [FiniteMagmaE677.fiber496,
            show ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x = 0 by
              rw [show ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x
                  = ((7 : ZMod 31)) * (y - x) from by ring, hd0]
              ring]
        have e4 : FiniteMagmaE677.fiber496 ζ ω y ((3 : ZMod 31) * x
            - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y)) t
            ((1 + ζ) * s + ζ * ((1 + ζ) * ((1 + ζ) * t + ζ * s) + ζ * t))
            = (1 + ζ) * t + ζ * ((1 + ζ) * s + ζ * ((1 + ζ) * ((1 + ζ) * t + ζ * s) + ζ * t)) := by
          simp [FiniteMagmaE677.fiber496,
            show ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
              - 2 * y)) - y = 0 by
              rw [show ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
                  - 2 * y)) - y = ((-15 : ZMod 31)) * (y - x) from by ring, hd0]
              ring]
        rw [e1, e2, e3, e4]
        linear_combination -(s + t) * hζ + (s - ζ ^ 3 * t) * h2
      rcases hfermat (y - x) with h0' | hq | hq
      · exact absurd h0' hd0
      · -- y - x is a square: nodes 1,2 (character -1) use ω; nodes 3,4 (character 1) project
        have n1 : x - y = (-1 : ZMod 31) * (y - x) := by ring
        have n1ne : x - y ≠ 0 := fun h => hd0 (hu1 _ (n1 ▸ h))
        have n1p : (x - y) ^ 15 ≠ 1 := by
          rw [n1, mul_pow, hneg1, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have n2 : y - ((3 : ZMod 31) * y - 2 * x) = (-2 : ZMod 31) * (y - x) := by ring
        have n2ne : y - ((3 : ZMod 31) * y - 2 * x) ≠ 0 := fun h => hd0 (hu2 _ (n2 ▸ h))
        have n2p : (y - ((3 : ZMod 31) * y - 2 * x)) ^ 15 ≠ 1 := by
          rw [n2, mul_pow, hn2p, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have n3 : ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x
            = ((7 : ZMod 31)) * (y - x) := by ring
        have n3ne : ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x ≠ 0 :=
          fun h => hd0 (hu7 _ (n3 ▸ h))
        have n3p : (((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x) ^ 15 = 1 := by
          rw [n3, mul_pow, h7_15, hq]
          norm_num
        have n4 : ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y = ((-15 : ZMod 31)) * (y - x) := by ring
        have n4ne : ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y ≠ 0 := fun h => hd0 (hu15 _ (n4 ▸ h))
        have n4p : (((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y) ^ 15 = 1 := by
          rw [n4, mul_pow, hn15p, hq]
          norm_num
        have e1 : FiniteMagmaE677.fiber496 ζ ω y x t s = (1 + ω) * t + ω * s := by
          simp [FiniteMagmaE677.fiber496, n1ne, n1p]
        have e2 : FiniteMagmaE677.fiber496 ζ ω ((3 : ZMod 31) * y - 2 * x) y
            ((1 + ω) * t + ω * s) t = (1 + ω) * ((1 + ω) * t + ω * s) + ω * t := by
          simp [FiniteMagmaE677.fiber496, n2ne, n2p]
        have e3 : FiniteMagmaE677.fiber496 ζ ω x ((3 : ZMod 31) * ((3 : ZMod 31) * y
            - 2 * x) - 2 * y) s ((1 + ω) * ((1 + ω) * t + ω * s) + ω * t)
            = ((1 + ω) * ((1 + ω) * t + ω * s) + ω * t) := by
          simp [FiniteMagmaE677.fiber496, n3ne, n3p]
        have e4 : FiniteMagmaE677.fiber496 ζ ω y ((3 : ZMod 31) * x
            - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y)) t
            ((1 + ω) * ((1 + ω) * t + ω * s) + ω * t)
            = ((1 + ω) * ((1 + ω) * t + ω * s) + ω * t) := by
          simp [FiniteMagmaE677.fiber496, n4ne, n4p]
        rw [e1, e2, e3, e4]
        linear_combination -(s + t) * hω + (s - ω * t) * h2
      · -- y - x is a non-square: nodes 1,2 project; nodes 3,4 use ω
        have n1 : x - y = (-1 : ZMod 31) * (y - x) := by ring
        have n1ne : x - y ≠ 0 := fun h => hd0 (hu1 _ (n1 ▸ h))
        have n1p : (x - y) ^ 15 = 1 := by
          rw [n1, mul_pow, hneg1, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have n2 : y - ((3 : ZMod 31) * y - 2 * x) = (-2 : ZMod 31) * (y - x) := by ring
        have n2ne : y - ((3 : ZMod 31) * y - 2 * x) ≠ 0 := fun h => hd0 (hu2 _ (n2 ▸ h))
        have n2p : (y - ((3 : ZMod 31) * y - 2 * x)) ^ 15 = 1 := by
          rw [n2, mul_pow, hn2p, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have n3 : ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x
            = ((7 : ZMod 31)) * (y - x) := by ring
        have n3ne : ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x ≠ 0 :=
          fun h => hd0 (hu7 _ (n3 ▸ h))
        have n3p : (((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y) - x) ^ 15 ≠ 1 := by
          rw [n3, mul_pow, h7_15, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have n4 : ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y = ((-15 : ZMod 31)) * (y - x) := by ring
        have n4ne : ((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y ≠ 0 := fun h => hd0 (hu15 _ (n4 ▸ h))
        have n4p : (((3 : ZMod 31) * x - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x)
            - 2 * y)) - y) ^ 15 ≠ 1 := by
          rw [n4, mul_pow, hn15p, hq]
          first | (norm_num; try decide) | exact hneg1ne
        have e1 : FiniteMagmaE677.fiber496 ζ ω y x t s = s := by
          simp [FiniteMagmaE677.fiber496, n1ne, n1p]
        have e2 : FiniteMagmaE677.fiber496 ζ ω ((3 : ZMod 31) * y - 2 * x) y s t = t := by
          simp [FiniteMagmaE677.fiber496, n2ne, n2p]
        have e3 : FiniteMagmaE677.fiber496 ζ ω x ((3 : ZMod 31) * ((3 : ZMod 31) * y
            - 2 * x) - 2 * y) s t = (1 + ω) * s + ω * t := by
          simp [FiniteMagmaE677.fiber496, n3ne, n3p]
        have e4 : FiniteMagmaE677.fiber496 ζ ω y ((3 : ZMod 31) * x
            - 2 * ((3 : ZMod 31) * ((3 : ZMod 31) * y - 2 * x) - 2 * y)) t
            ((1 + ω) * s + ω * t) = (1 + ω) * t + ω * ((1 + ω) * s + ω * t) := by
          simp [FiniteMagmaE677.fiber496, n4ne, n4p]
        rw [e1, e2, e3, e4]
        linear_combination -(s + t) * hω + s * h2
  · -- not right-cancellative: the difference 1 is a square, so the fiber projects
    refine ⟨(0, (0 : M)), (0, (1 : M)), (1, 0), ?_, ?_⟩
    · show FiniteMagmaE677.magma496 ζ ω (0, (0 : M)) (1, 0)
          = FiniteMagmaE677.magma496 ζ ω (0, (1 : M)) (1, 0)
      have hval : ∀ m : M, FiniteMagmaE677.fiber496 ζ ω 0 1 m 0 = 0 := by
        intro m
        simp only [FiniteMagmaE677.fiber496]
        rw [if_neg (show ¬(((1 : ZMod 31) - (0 : ZMod 31)) = 0) from by decide),
            if_pos (show ((1 : ZMod 31) - (0 : ZMod 31)) ^ 15 = 1 from by decide)]
      simp only [FiniteMagmaE677.magma496]
      rw [hval, hval]
    · intro h
      exact h01 (congrArg Prod.snd h)

theorem solution {M : Type v} [CommRing M] (ζ ω : M)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hω : ω ^ 2 + ω + 1 = 0)
    (h2 : (1 : M) + 1 = 0) (h01 : (0 : M) ≠ 1) :
    FiniteMagmaE677.E677 (FiniteMagmaE677.magma496 ζ ω) ∧
    ∃ a b c : ZMod 31 × M,
      FiniteMagmaE677.magma496 ζ ω a c = FiniteMagmaE677.magma496 ζ ω b c ∧ a ≠ b :=
  FiniteMagmaE677.magma496_generic ζ ω hζ hω h2 h01
