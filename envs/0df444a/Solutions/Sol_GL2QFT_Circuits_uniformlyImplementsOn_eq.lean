-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_eq
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:38:57.11688+00:00
-- url     : https://prove2.me/submissions/83077b36-0353-4cc5-a373-205dccae6239

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

theorem solution {P : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)]
    [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)}
    {cout : ∀ D, Y D → Qubits (outW D)} {Φ Φ' : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : UniformlyImplementsOn P cin cout Φ) (heq : ∀ D, P D → Φ D = Φ' D) :
    UniformlyImplementsOn P cin cout Φ' := by
  rcases h with ⟨wires, circ, f, c, hf, henc, hlen, himpl⟩
  refine ⟨wires, circ, f, c, hf, henc, hlen, fun D hD k => ?_⟩
  rw [← heq D hD]
  exact himpl D hD k
