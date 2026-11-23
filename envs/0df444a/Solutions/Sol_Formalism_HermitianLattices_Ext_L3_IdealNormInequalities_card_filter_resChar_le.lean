-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.card_filter_resChar_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:14.305613+00:00
-- url     : https://prove2.me/submissions/02905b4b-5dc5-479c-8198-4d7e9c83f0ba

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_span_resChar
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_under_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_under_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]
set_option linter.deprecated false
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by

  classical
  by_cases hn : ∃ P ∈ s, resChar P.1 = n
  · obtain ⟨P0, -, hP0⟩ := hn
    have hJ : Ideal.span {((n : ℕ) : ℤ)} = P0.1.under ℤ := by
      rw [← hP0]
      exact span_resChar P0.1
    haveI : (Ideal.span {((n : ℕ) : ℤ)}).IsMaximal := by
      rw [hJ]
      exact under_isMaximal P0.2
    have hJne : Ideal.span {((n : ℕ) : ℤ)} ≠ ⊥ := by
      rw [hJ]
      exact under_ne_bot P0.2
    calc (s.filter (fun P => resChar P.1 = n)).card
        ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((n : ℕ) : ℤ)}) (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn (fun P => P.1) (by
            intro P hP
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hJne]
            obtain ⟨-, hPn⟩ := Finset.mem_filter.mp hP
            refine ⟨P.2.isPrime, ⟨?_⟩⟩
            rw [← hPn]
            exact span_resChar P.1) (fun a _ b _ h => Subtype.ext h)
      _ ≤ finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hJne
  · push_neg at hn
    rw [Finset.filter_false_of_mem (fun P hP => hn P hP)]
    simp
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
