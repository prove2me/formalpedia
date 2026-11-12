-- Prove2me | solution 1 for BunkbedFalse.robust_hyperedge
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T00:09:02.694443+00:00
-- url     : https://prove2.me/submissions/85c1c3b0-1763-4532-8d11-7973da67caab

import Theorems.Thm_BunkbedFalse_wz_diff_poly
import Theorems.Thm_BunkbedFalse_wzDiffPoly_pos

open Bunkbed Bunkbed.Hyper

theorem solution (P : WZ → ℚ)
    (hnn : ∀ s, 0 ≤ P s)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1)
    (hsym : P .ab_c = P .ac_b)
    (hpos : 0 < P .abc * P .a_b_c - P .ab_c * P .ac_b)
    (h400 : 400 * P .a_bc ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      < wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) := by
  rw [← hsym] at hsum hpos h400
  have hd := BunkbedFalse.wz_diff_poly P hsym
  have hp : 0 < wzDiffPoly (P .abc) (P .a_b_c) (P .a_bc) (P .ab_c) :=
    BunkbedFalse.wzDiffPoly_pos _ _ _ _ (hnn _) (hnn _) (hnn _) (hnn _)
      (by linarith) hpos h400
  linarith
