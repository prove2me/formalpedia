-- Prove2me | solution 1 for Erdos1219.aleph_omega_le_of_forall_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:27.258659+00:00
-- url     : https://prove2.me/submissions/27be3d75-ec0e-472b-8711-ab2ed37971bd

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {c : Cardinal.{u}}
    (h : ∀ N : ℕ, ℵ_ (N : Ordinal.{u}) ≤ c) : ℵ_ ω ≤ c := by
  rw [aleph_limit isSuccLimit_omega0]
  refine ciSup_le' fun a => ?_
  obtain ⟨N, hN⟩ := lt_omega0.1 a.2
  have : (a : Ordinal.{u}) = N := hN
  rw [this]
  exact h N
end Erdos1219
