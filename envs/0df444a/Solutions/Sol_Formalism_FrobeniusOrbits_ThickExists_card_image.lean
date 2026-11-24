-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.card_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:32.278141+00:00
-- url     : https://prove2.me/submissions/4dc41529-f056-4259-9a3d-3c6a3b233f7a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_coeff_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_cast_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.FrobeniusOrbits.ThickExists
private lemma sphere_mem_lemma {S d k : ℕ} {v : Fin S → ℕ} (hv : v ∈ Behrend.sphere S d k) :
    (∀ i, v i < d) ∧ ∑ i, v i ^ 2 = k := by
  simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv
  exact hv
end Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution (L S d k : ℕ) (hL : 1 ≤ L) :
    ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))).card =
      (Behrend.sphere S d k).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  obtain ⟨hbv, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hv)
  obtain ⟨hbw, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hw)
  have hc : ((Behrend.map (4 * L * d) v : ℕ) : ℤ) = ((Behrend.map (4 * L * d) w : ℕ) : ℤ) := by
    rw [hvw]
  rw [cast_map, cast_map] at hc
  have hbound : ∀ m : Fin S, |(v m : ℤ) - w m| < ((4 * L * d : ℕ) : ℤ) := by
    intro m
    have a1 : (v m : ℤ) < d := by exact_mod_cast hbv m
    have a2 : (w m : ℤ) < d := by exact_mod_cast hbw m
    have z1 : (0 : ℤ) ≤ v m := by positivity
    have z2 : (0 : ℤ) ≤ w m := by positivity
    have z3 : (0 : ℤ) ≤ d := by positivity
    have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith
  have hsum : ∑ m, ((v m : ℤ) - w m) * ((4 * L * d : ℕ) : ℤ) ^ (m : ℕ) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hc, sub_self]
  have hz := coeff_zero ((4 * L * d : ℕ) : ℤ) (fun m => (v m : ℤ) - w m) hbound hsum
  funext m
  have h0 : (v m : ℤ) - w m = 0 := hz m
  omega
end Formalism.FrobeniusOrbits.ThickExists
