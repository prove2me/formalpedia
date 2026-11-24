-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.corollary_mass_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:33.128979+00:00
-- url     : https://prove2.me/submissions/c7a7c83a-35a5-4b68-8d83-50f68aff0e72

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_chebyshev_moment_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentMassBound := by
  intro Ω _ μ _ r q l H1 la hm hpos hH1 hla hp hn
  have hsub : {ω | ∃ a, la * H1 ≤ max (l a ω) (l a ω)⁻¹} ⊆
      ⋃ a : Fin (r + 1), ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹}) := by
    rintro ω ⟨a, ha⟩
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    rcases le_max_iff.1 ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : ∀ a : Fin (r + 1), μ ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹}) ≤
      ENNReal.ofReal (2 / la ^ (2 * q)) := by
    intro a
    have h1 := chebyshev_moment_bound μ (l a) q H1 la (hm a) hH1 hla (hp a)
    have h2 := chebyshev_moment_bound μ (fun ω => (l a ω)⁻¹) q H1 la (hm a).inv hH1 hla (hn a)
    refine (measure_union_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le μ _).trans ?_)
  refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    show ((r + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((r : ℝ) + 1) by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end Formalism.HermitianLatticeCounting.P
