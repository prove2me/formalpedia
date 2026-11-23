-- Prove2me | solution 1 for Experiments.NSA.approx_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:18.175098+00:00
-- url     : https://prove2.me/submissions/a58b66a6-fc26-46f5-8556-d9ec0e802520

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution {u v : ℕ → E} :
    (u : Hyp E) ≈ₕ (v : Hyp E) ↔ Tendsto (fun n => u n - v n) (hyperfilter ℕ) (𝓝 0) :=
  Iff.rfl
end Experiments.NSA
