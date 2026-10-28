-- Prove2me | solution 1 for BitcoinMerkle.pairUp_append_even
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:01.997817+00:00
-- url     : https://prove2.me/submissions/ee94365b-7f24-4d72-b1de-a42e6b4b048b

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) :
    ∀ (l r : List H), l.length % 2 = 0 → BitcoinMerkle.pairUp c (l ++ r) = BitcoinMerkle.pairUp c l ++ BitcoinMerkle.pairUp c r
  | [], r, _ => by simp [pairUp]
  | [a], r, h => by simp at h
  | a :: b :: rest, r, h => by
    simp only [List.length_cons] at h
    have h' : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, pairUp, List.cons.injEq, true_and]
    exact solution c rest r h'
