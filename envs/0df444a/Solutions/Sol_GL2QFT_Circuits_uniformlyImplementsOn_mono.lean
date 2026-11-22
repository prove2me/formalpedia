-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:37:32.918626+00:00
-- url     : https://prove2.me/submissions/377ef0c2-33f7-456c-a0cb-68775e03dbee

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

theorem solution {P P' : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)]
    [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)}
    {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h : UniformlyImplementsOn P cin cout Φ) (himp : ∀ D, P' D → P D) :
    UniformlyImplementsOn P' cin cout Φ := by
  rcases h with ⟨wires, circ, f, c, hf, henc, hlen, himpl⟩
  exact ⟨wires, circ, f, c, hf, fun D hD => henc D (himp D hD),
    fun D hD => hlen D (himp D hD), fun D hD => himpl D (himp D hD)⟩
