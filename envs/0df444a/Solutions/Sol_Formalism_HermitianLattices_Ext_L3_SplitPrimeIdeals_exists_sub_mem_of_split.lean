-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.exists_sub_mem_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:50.966993+00:00
-- url     : https://prove2.me/submissions/80461412-cf90-49ff-94d2-ff01fe227b04

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_isMaximal_invol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) (b : B) : ∃ a : A, b - ι a ∈ P := by
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  rw [Ideal.mem_comap] at hv
  have hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v) := by rw [map_add, hσ, add_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  refine ⟨a, ?_⟩
  have hv' : v = 1 - u := by rw [← huv]; ring
  have : b - ι a = b * u - σ b * σ v := by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring
  rw [this]
  exact P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
