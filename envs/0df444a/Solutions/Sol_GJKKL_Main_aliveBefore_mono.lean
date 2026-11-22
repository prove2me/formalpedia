-- Prove2me | solution 1 for GJKKL.Main.aliveBefore_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:56.040195+00:00
-- url     : https://prove2.me/submissions/dbd41516-5e68-42cc-b1c1-2a2bab52a065

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
theorem _root_.solution {α : Type*} {G G' : List α → Prop} (hGG : ∀ h, G h → G' h) :
    ∀ h, AliveBefore G h → AliveBefore G' h
  | [], _ => trivial
  | _ :: h, hal => ⟨solution hGG h hal.1, hGG h hal.2⟩
end GJKKL.Main
