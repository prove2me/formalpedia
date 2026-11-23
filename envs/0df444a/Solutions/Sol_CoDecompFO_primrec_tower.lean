-- Prove2me | solution 1 for CoDecompFO.primrec_tower
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:02.31362+00:00
-- url     : https://prove2.me/submissions/3b14d72c-8288-4449-b6cd-d5bcad21686e

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Mathlib.Computability.Partrec

set_option autoImplicit false

open CoDecompFO

private theorem primrec_pow_local : Primrec₂ (fun m n : ℕ => m ^ n) := by
  have h := Primrec.nat_rec (f := fun _ : ℕ => 1)
    (g := fun m (p : ℕ × ℕ) => p.2 * m) (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  apply Primrec.of_eq h
  rintro ⟨m, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ] at ih ⊢
      exact congrArg (fun z => z * m) ih

/-- The explicit tower bound is primitive recursive in the width, atom count, and level. -/
theorem solution : Primrec (fun a : (ℕ × ℕ) × ℕ => tower a.1.1 a.1.2 a.2) := by
  have h0 : Primrec (fun a : ℕ × ℕ => 2 ^ (2 ^ a.2)) :=
    primrec_pow_local.comp (Primrec.const 2)
      (primrec_pow_local.comp (Primrec.const 2) Primrec.snd)
  have hg : Primrec₂ (fun (a : ℕ × ℕ) (p : ℕ × ℕ) =>
      2 ^ (a.1 * 2 ^ (a.1 * p.2))) :=
    primrec_pow_local.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
        (primrec_pow_local.comp (Primrec.const 2)
          (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.snd.comp Primrec.snd))))
  apply Primrec.of_eq ((Primrec.nat_rec h0 hg).comp Primrec.fst Primrec.snd)
  rintro ⟨⟨w, q⟩, m⟩
  induction m with
  | zero => rfl
  | succ m ih => simp only [tower, ih]
