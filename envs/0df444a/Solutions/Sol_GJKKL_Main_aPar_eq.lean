-- Prove2me | solution 1 for GJKKL.Main.aPar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:19.362153+00:00
-- url     : https://prove2.me/submissions/327cf0ab-981f-46a9-92d1-f2a5ebd0dc28

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics
namespace GJKKL.Main
theorem _root_.solution {V : Type*} [Fintype V] {k : ℕ} (hk0 : (k : ℝ) ≠ 0)
    (hn0 : (Fintype.card V : ℝ) ≠ 0) (t : ℕ) :
    aPar V k t = (Fintype.card V : ℝ) / k * pfrac ((Fintype.card V : ℝ) / k) t := by
  unfold aPar pfrac
  first | (field_simp; ring) | field_simp
end GJKKL.Main
