-- Prove2me | solution 1 for CertDRO.NNSmooth.proposition_5_part_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:59:31.31223+00:00
-- url     : https://prove2.me/submissions/0e91b3af-b5a4-49de-a01b-aa4e03b04abc

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

set_option autoImplicit false

open CertDRO.NNSmooth CertDRO.NNSmooth.Network

theorem solution (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ)
    (hE : N.AssumptionE L L0 L1) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0), ‖N.F l x - N.F l x'‖ ≤ N.α L0 l * ‖x - x'‖ := by
  intro l
  induction l with
  | zero =>
    intro _ x x'
    simp [Network.α, Network.F]
  | succ l ih =>
    intro hl x x'
    have h1 := ih (by omega) x x'
    have hL0 : 0 ≤ L0 l := (hE.L0_pos l (by omega)).le
    have h2 := hE.lipschitz l (by omega) (N.θ l (N.F l x)) (N.θ l (N.F l x'))
    have h3 : ‖N.θ l (N.F l x) - N.θ l (N.F l x')‖ ≤ ‖N.θ l‖ * ‖N.F l x - N.F l x'‖ := by
      rw [← map_sub]; exact (N.θ l).le_opNorm _
    have h4 : N.F (l + 1) x - N.F (l + 1) x' = N.σ l (N.θ l (N.F l x)) - N.σ l (N.θ l (N.F l x')) := rfl
    rw [h4]
    have hα : N.α L0 (l + 1) = L0 l * ‖N.θ l‖ * N.α L0 l := by
      unfold Network.α
      rw [Finset.prod_range_succ]; ring
    rw [hα]
    calc _ ≤ L0 l * ‖N.θ l (N.F l x) - N.θ l (N.F l x')‖ := h2
      _ ≤ L0 l * (‖N.θ l‖ * ‖N.F l x - N.F l x'‖) := by gcongr
      _ ≤ L0 l * (‖N.θ l‖ * (N.α L0 l * ‖x - x'‖)) := by gcongr
      _ = _ := by ring
