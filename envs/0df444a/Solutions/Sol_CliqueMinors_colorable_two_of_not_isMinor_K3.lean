-- Prove2me | solution 1 for CliqueMinors.colorable_two_of_not_isMinor_K3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:27.500794+00:00
-- url     : https://prove2.me/submissions/11e17be1-f7d9-4c26-b81e-f2615f691fa5

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_mono
public import Theorems.Thm_CliqueMinors_exists_low_deg_K3
public import Theorems.Thm_CliqueMinors_color_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
namespace CliqueMinors
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 := by
  have := Fintype.ofFinite V
  exact color_aux 2 (by norm_num) (fun G => ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G)
    (fun _ _ hle hG h' => hG (isMinor_mono hle h')) exists_low_deg_K3 _ G Finset.univ rfl
    (fun _ _ _ => Finset.mem_univ _) h
end CliqueMinors
