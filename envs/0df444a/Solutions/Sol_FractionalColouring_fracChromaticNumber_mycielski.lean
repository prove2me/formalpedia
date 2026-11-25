-- Prove2me | solution 1 for FractionalColouring.fracChromaticNumber_mycielski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:57:48.237793+00:00
-- url     : https://prove2.me/submissions/fac37bd4-c84d-4de2-a7c1-73484f1adf9b

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_fracChromaticNumber_mycielski_le
public import Theorems.Thm_FractionalColouring_le_fracChromaticNumber_mycielski

set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
variable (G)
namespace FractionalColouring
theorem _root_.solution [Nonempty V] :
    fracChromaticNumber (graph G) = fracChromaticNumber G + 1 / fracChromaticNumber G :=
  le_antisymm fracChromaticNumber_mycielski_le le_fracChromaticNumber_mycielski
end FractionalColouring
