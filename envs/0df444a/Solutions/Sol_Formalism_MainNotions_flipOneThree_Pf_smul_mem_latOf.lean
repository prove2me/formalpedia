-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.smul_mem_latOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:42.739302+00:00
-- url     : https://prove2.me/submissions/8e6b4083-75ff-464c-9fcf-951d5dce443c

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (R : Subring K) (g : GL (Fin k) K) {c : K} (hc : c ∈ R)
    {f : PolXY K k} (hf : f ∈ latOf g (GaussLat R)) : c • f ∈ latOf g (GaussLat R) := by
  simp only [Formalism.CountingSumsFrames.latOf, Set.mem_image] at hf ⊢
  obtain ⟨h, hh, rfl⟩ := hf
  refine ⟨c • h, ?_, map_smul (Formalism.CountingSumsFrames.glAct g) c h⟩
  show ∀ m, coeff m (c • h) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact R.mul_mem hc (hh m)
end Formalism.MainNotions.flipOneThree.Pf
