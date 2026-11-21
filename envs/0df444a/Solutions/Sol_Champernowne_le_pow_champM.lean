-- Prove2me | solution 1 for Champernowne.le_pow_champM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:38:52.690766+00:00
-- url     : https://prove2.me/submissions/5c78a08f-bf48-4439-bc82-ec4b6b7bdd49

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n : ℕ) :
    champIndex b n + 1 ≤ b ^ champM b n :=
  le_of_lt (Nat.lt_pow_succ_log_self hb _)
end Champernowne
