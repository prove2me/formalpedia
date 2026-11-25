-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.idx_smLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:07.142539+00:00
-- url     : https://prove2.me/submissions/fb97066b-f1d7-4a26-bda1-13b7f64c4593

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_map_isLattice
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_idxB
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_sm_surj
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_loc_smLat_le
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_one
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_pow
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_DivisionValues_index_change_formula
import Theorems.Thm_Formalism_DivisionValues_semilocal_basis_exists


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
open exponent_index_lattice RationalHermitianForm
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {D : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) (Fin D → K))
    (hA : Submodule.IsLattice K A) {a : K} (ha : a ≠ 0) :
    idx w A (smLat a A) = (D : ℤ) * vw w a := by
  obtain ⟨f, hf⟩ := semilocal_basis_exists K D A hA w
  have haA : Submodule.IsLattice K (smLat a A) := map_isLattice (sm D a) (sm_surj D ha) A hA
  have hspK : Submodule.span K (Set.range f) = ⊤ :=
    hf.1.span_eq_top_of_card_eq_finrank' (by simp)
  have hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f)) :=
    ⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩
  have hone_f : (fun i => ∑ k, (1 : Matrix (Fin D) (Fin D) K) k i • f k) = f := by
    funext i
    simp [Matrix.one_apply]
  have ha_f : (fun i => ∑ k, (a • (1 : Matrix (Fin D) (Fin D) K)) k i • f k) = fun i => a • f i := by
    funext i
    simp [Matrix.one_apply]
  have i1 := (index_change_formula K D A hA f hf.1 w 1 (by rw [hone_f]; exact hf)).1
  have hspan_af : Submodule.span (𝓞 K) (Set.range fun i => a • f i) =
      smLat a (Submodule.span (𝓞 K) (Set.range f)) := by
    unfold smLat
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hloc : IsLocBasis (smLat a A) w (fun i => a • f i) := by
    refine ⟨?_, ?_⟩
    · exact hf.1.units_smul (fun _ => Units.mk0 a ha)
    · rw [hspan_af]
      exact le_antisymm (loc_smLat_le a _ hf.2.le) (loc_smLat_le a _ hf.2.ge)
  have i2 := (index_change_formula K D (smLat a A) haA f hf.1 w (a • 1) (by rw [ha_f]; exact hloc)).1
  rw [Matrix.det_one, ValuationRepresentative.vw_one] at i1
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ReductionFirst.vw_pow] at i2
  have h := idxB w A (Submodule.span (𝓞 K) (Set.range f)) (smLat a A) hA hspan_f haA
  rw [h.2.1, h.1, i1, i2]
  ring
end Formalism.DivisionValues.exponent_index_lattice
