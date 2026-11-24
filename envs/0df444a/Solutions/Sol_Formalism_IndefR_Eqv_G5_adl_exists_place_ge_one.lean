-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_exists_place_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.242664+00:00
-- url     : https://prove2.me/submissions/a9b12c60-3f2b-42a9-a641-8d9ed82a0f1f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ w : InfinitePlace F, 1 ≤ w (r : F) := by
  classical
  by_contra h
  push_neg at h
  have hnn : ∀ w : InfinitePlace F, 0 ≤ w (r : F) := fun w => by
    first | positivity | exact w.nonneg _ | exact InfinitePlace.nonneg w _
  have hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (r : F)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.mpr hr
    have := Int.one_le_abs hz
    exact_mod_cast this
  rw [← InfinitePlace.prod_eq_abs_norm] at hN
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at hN
  have h1 : w0 (r : F) ^ w0.mult < 1 := pow_lt_one₀ (hnn w0) (h w0) InfinitePlace.mult_pos.ne'
  have h2 : ∏ w ∈ Finset.univ.erase w0, w (r : F) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (h w).le)
  have h3 : 0 ≤ w0 (r : F) ^ w0.mult := pow_nonneg (hnn w0) _
  nlinarith
end Formalism.IndefR.Eqv.G5
