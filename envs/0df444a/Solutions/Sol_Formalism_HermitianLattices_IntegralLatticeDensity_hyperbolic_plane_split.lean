-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.hyperbolic_plane_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:46.067593+00:00
-- url     : https://prove2.me/submissions/9de0d27f-cd87-42a5-8a06-dc83fa0b446d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset PD
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : HyperbolicSplit := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'

  have hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) →
      ∑ i, φ (∑ e, g e i • w e) = 0 := by
    intro g w hg
    have hz : ∀ e, ∑ i, nm (g e i) = 0 := by
      intro e
      apply hinj
      rw [map_sum, map_zero]
      simpa [hnm] using hg e e
    rw [diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]
    simp [hz]

  have hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e) := by
    simp_rw [cob_sum_left' h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t',
      Finset.sum_eq_single e]
    · rw [hff' e e, if_pos rfl, one_smul]
    · intro e' _ hne
      rw [hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]
    · intro h
      exact absurd (Finset.mem_univ e) h
  calc ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e))
      = ∑ i, (φ (∑ e, f e i • t e) + φ (∑ e, f' e i • t' e) +
          cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, phi_add' (φ := φ)]
    _ = ∑ e, cob φ (t e) (t' e) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross,
          zero_add, zero_add]
end Formalism.HermitianLattices.IntegralLatticeDensity
