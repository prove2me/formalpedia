-- Prove2me | solution 1 for Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_loc_iff_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:59.732706+00:00
-- url     : https://prove2.me/submissions/a54a06b3-e2af-4d19-ac03-a3cfc278d180

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Theorems.Thm_P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5
import Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_A
import Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_algebraMap_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔ x ∈ Submodule.span (A w) (M : Set (Fin d → K)) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero w hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A w := (mem_A w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_loc_iff' w M y).mpr ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_loc_iff' w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A w a).mp a.2
      refine (mem_loc_iff' w M _).mpr ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
