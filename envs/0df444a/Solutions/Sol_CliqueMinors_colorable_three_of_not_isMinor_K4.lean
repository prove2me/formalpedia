-- Prove2me | solution 1 for CliqueMinors.colorable_three_of_not_isMinor_K4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:59.831773+00:00
-- url     : https://prove2.me/submissions/adc09282-f77e-480b-acd2-e2e69f03fe96

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_mono
public import Theorems.Thm_CliqueMinors_exists_low_deg_K4
public import Theorems.Thm_CliqueMinors_color_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
namespace CliqueMinors
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 := by
  have := Fintype.ofFinite V
  exact color_aux 3 (by norm_num) (fun G => ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G)
    (fun _ _ hle hG h' => hG (isMinor_mono hle h')) exists_low_deg_K4 _ G Finset.univ rfl
    (fun _ _ _ => Finset.mem_univ _) h
end CliqueMinors
