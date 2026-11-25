-- Prove2me | solution 1 for CompanionTheory.CapEig.rw_cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:49.945332+00:00
-- url     : https://prove2.me/submissions/1a1789e1-c647-41cf-9ba1-ad151cb7a189

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefCC
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}
namespace CompanionTheory.CapEig
theorem _root_.solution (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) {f : B.Mat k r → E}
    (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G, B.Rw v f g = cf σ x₀ a (dsW σ v b) g
  | [], _, g, hg => hf g hg
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v f (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v f (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [solution h x₀ a hb hf hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv
end CompanionTheory.CapEig
