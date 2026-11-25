-- Prove2me | solution 1 for Formalism.MainNotions.UnitaryGroupLocal.sigR_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:22:02.870966+00:00
-- url     : https://prove2.me/submissions/df88ff13-c578-46a1-8f6d-bf818a854207

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApprox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnitaryGroupLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnitaryGroupLocal
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain Topology Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.MainNotions.UnitaryGroupLocal
theorem _root_.solution (σ : E →ₐ[F] E) {x : E ⊗[F] v.adicCompletion F} (hx : x ∈ oE v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) x ∈ oE v := by
  refine Subring.closure_induction (p := fun x _ => PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) x ∈ oE v)
    (fun x hx => ?_) (by simp) (by simp) (fun x y _ _ hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun x _ hx => by rw [map_neg]; exact neg_mem hx) (fun x y _ _ hx hy => by rw [map_mul]; exact mul_mem hx hy) hx
  rcases hx with ⟨⟨e, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨r, hr⟩, rfl⟩
  · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E y), ?_⟩, ?_⟩)
    · obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = σ (algebraMap (𝓞 E) E y) :=
        ⟨⟨σ (algebraMap (𝓞 E) E y), (y.2.map (σ.restrictScalars ℚ))⟩, rfl⟩
      exact ⟨z, hz⟩
    · simp [PI.UnitaryApproxDefs.sigR]
  · exact Subring.subset_closure (Or.inr ⟨⟨r, hr⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩)
end Formalism.MainNotions.UnitaryGroupLocal
