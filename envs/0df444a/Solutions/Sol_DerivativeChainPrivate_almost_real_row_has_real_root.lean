-- Prove2me | solution 1 for DerivativeChainPrivate.almost_real_row_has_real_root
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:53:25.212977+00:00
-- url     : https://prove2.me/submissions/8f02fd01-d8bc-4538-8a35-60221d23a7af

import Theorems.Thm_DerivativeChainPrivate_almost_real_row_count

set_option autoImplicit false
open DerivativeChainPrivate

theorem solution {n m : ℕ} (a : Fin n → ℂ) (hr : RealCoefficients a)
    (hm : m ≤ n) (hc : nonrealCount a < m) :
    ∃ x : ℝ, (row a m).eval (x : ℂ) = 0 := by
  obtain ⟨p, _, hrows⟩ := DerivativeChainPrivate.almost_real_row_count a hr
  obtain ⟨hmap, hdegree, hcount⟩ := hrows m hm
  have hpos : 0 < ((Polynomial.derivative^[n - m]) p).roots.card := by omega
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  have hne : (Polynomial.derivative^[n - m]) p ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hdegree
    omega
  have heval : ((Polynomial.derivative^[n - m]) p).eval x = 0 :=
    (Polynomial.mem_roots hne).mp hx
  refine ⟨x, ?_⟩
  rw [← hmap]
  change (((Polynomial.derivative^[n - m]) p).map Complex.ofRealHom).eval
    (Complex.ofRealHom x) = 0
  rw [Polynomial.eval_map_apply, heval, map_zero]
