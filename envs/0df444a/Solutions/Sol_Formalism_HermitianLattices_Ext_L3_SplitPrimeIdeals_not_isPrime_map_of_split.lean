-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.not_isPrime_map_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:18.854646+00:00
-- url     : https://prove2.me/submissions/2a4fa5a8-cfd5-4624-bcc3-beb815cbe481

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_isMaximal_invol
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431

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
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) : ¬ ((P.comap ι).map ι).IsPrime := by
  intro hpr
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  have hu' : u ∉ P.comap σ := by
    intro h
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))
  have hle1 : (P.comap ι).map ι ≤ P := Ideal.map_comap_le
  have hle2 : (P.comap ι).map ι ≤ P.comap σ := by
    rw [← comap_ι_comap hfix P]
    exact Ideal.map_comap_le
  have hfx : σ (u * σ u) = u * σ u := by rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  have hmem : u * σ u ∈ (P.comap ι).map ι := by
    rw [← ha]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ha]
    exact P.mul_mem_right _ hu
  rcases hpr.mem_or_mem hmem with h1 | h1
  · exact hu' (hle2 h1)
  · exact hu' (by rw [Ideal.mem_comap]; exact hle1 h1)
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
