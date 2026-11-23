-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.idx_change_img
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:37.663158+00:00
-- url     : https://prove2.me/submissions/ef4f577d-f904-4918-8377-c1f8745e2f99

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Theorems.Thm_Formalism_DivisionValues_StepBAux_image_li
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_lattice
import Theorems.Thm_Formalism_DivisionValues_StepBAux_isLocBasis_image
import Theorems.Thm_Formalism_DivisionValues_StepBAux_localization_eq_and_conj_eq_of_semilocalization_eq
import Theorems.Thm_Formalism_DivisionValues_StepBAux_lidx_congr
import Theorems.Thm_Formalism_DivisionValues_StepBAux_exists_coords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (hIC : IdxChange) {d : ℕ} (ι0 ι1 : Matrix (Fin d) (Fin d) K)
    (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det) (L0 L1 : Submodule (𝓞 K) (Fin d → K))
    (hL1 : Submodule.IsLattice K L1) (w : HeightOneSpectrum (𝓞 K))
    (e0 e1 : Fin d → Fin d → K) (he0 : IsLocBasis L0 w e0) (he1 : IsLocBasis L1 w e1) :
    ∃ γ : Matrix (Fin d) (Fin d) K,
      (fun i => ι1 *ᵥ e1 i) = (fun i => ∑ k, γ k i • (ι0 *ᵥ e0 k)) ∧
      idx w (matLat ι0 L0) (matLat ι1 L1) = vw w γ.det ∧
      idx (conjPl w) (matLat ι0 L0) (matLat ι1 L1) = vw (conjPl w) γ.det := by
  have li0 := image_li ι0 hι0 e0 he0.1
  obtain ⟨γ, hγ⟩ := exists_coords _ li0 (fun i => ι1 *ᵥ e1 i)
  have hlb0 := isLocBasis_image ι0 hι0 L0 w e0 he0
  have hlb1 := isLocBasis_image ι1 hι1 L1 w e1 he1
  rw [hγ] at hlb1
  obtain ⟨h1, h2⟩ := hIC K d (matLat ι1 L1) (matLat_lattice ι1 hι1 L1 hL1) _ li0 w γ hlb1
  obtain ⟨p1, p2⟩ := localization_eq_and_conj_eq_of_semilocalization_eq w _ _ hlb0.2
  refine ⟨γ, hγ, ?_, ?_⟩
  · rw [← h1]
    exact lidx_congr _ _ _ _ _ p1.symm rfl
  · rw [← h2]
    exact lidx_congr _ _ _ _ _ p2.symm rfl
end Formalism.DivisionValues.StepBAux
