-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.character_unit_split_or_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:56.656687+00:00
-- url     : https://prove2.me/submissions/c0392928-c413-4013-ae2b-ce1f66447424

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Theorems.Thm_Formalism_HermitianLattices_IntegralLatticeDensity_half_orbit_count
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
private theorem sum_filter_val_eq_zero_of_balanced_sign_split {α : Type} [Fintype α] [DecidableEq α] (p : α → Prop)
    {inst : DecidablePred p} (O C : Finset α) (e : ℤ) (val : α → ℤ) (hdisj : Disjoint O C)
    (hO : ∀ τ ∈ O, val τ = e) (hC : ∀ τ ∈ C, val τ = -e)
    (hR : ∀ τ, τ ∉ O → τ ∉ C → val τ = 0)
    (h2 : 2 * (O.filter p).card = O.card) (h3 : 2 * (C.filter p).card = O.card) :
    ∑ τ ∈ univ.filter p, val τ = 0 := by
  have key : ∀ τ, val τ = (if τ ∈ O then e else 0) + (if τ ∈ C then -e else 0) := by
    intro τ
    by_cases h1 : τ ∈ O
    · have h1' : τ ∉ C := Finset.disjoint_left.1 hdisj h1
      simp [h1, h1', hO τ h1]
    · by_cases h1' : τ ∈ C
      · simp [h1, h1', hC τ h1']
      · simp [h1, h1', hR τ h1 h1']
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_ite_mem, Finset.sum_const, Finset.sum_const]
  have hA : (univ.filter p ∩ O).card = (O.filter p).card := by
    congr 1
    ext τ
    simp [and_comm]
  have hB : (univ.filter p ∩ C).card = (C.filter p).card := by
    congr 1
    ext τ
    simp [and_comm]
  rw [hA, hB, show (O.filter p).card = (C.filter p).card by omega]
  simp
end Formalism.HermitianLattices.IntegralLatticeDensity
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : ChiUnitSplitInert := by
  unfold ChiUnitSplitInert
  intro Emb _ φ c κ τ₀ hφ hc hdisj e val hO hC hR
  classical
  obtain ⟨-, h2, h3⟩ := half_orbit_count Emb φ c κ τ₀ hφ hc
  exact sum_filter_val_eq_zero_of_balanced_sign_split _ _ _ e val hdisj hO hC hR h2 h3
end Formalism.HermitianLattices.IntegralLatticeDensity
