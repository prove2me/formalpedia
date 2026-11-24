-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.mem_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:51.6018+00:00
-- url     : https://prove2.me/submissions/85c5b356-aeba-4034-b9a3-86df77e2ea74

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_psi_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mul_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_exp_eq_one_iff_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_add_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_lstd_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat
namespace Formalism.FourierDecayAlt.P.PBC.Lat
theorem _root_.solution (f : ℕ) (R : ℝ) (hR : 0 < R) (σ : crystallineComparison.V f) :
    σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
      ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hgen : ∀ v (β : Bool), crystallineComparison.psi (σ * gen f R (v, β)) = 1 ↔
      ∃ n : ℤ, (if β then -(2 * R * (σ v).im) else 2 * R * (σ v).re) = n := by
    intro v β
    rw [gen, mul_single, psi_single, add_conj, ← exp_eq_one_iff_int]
    congr! 4
    cases β <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  constructor
  · intro h v
    obtain ⟨a, ha⟩ := (hgen v false).1 (h _ (Submodule.subset_span ⟨(v, false), rfl⟩))
    obtain ⟨c, hc⟩ := (hgen v true).1 (h _ (Submodule.subset_span ⟨(v, true), rfl⟩))
    simp only [if_false, if_true, Bool.false_eq_true] at ha hc
    refine ⟨a, -c, ?_⟩
    rw [eq_div_iff (by simp [hR'])]
    apply Complex.ext
    · simp [Complex.mul_re]; linarith
    · simp [Complex.mul_im]; linarith
  · intro h z hz
    have hle : Lstd f R ≤ AddSubgroup.toIntSubmodule (kerPsi σ) := by
      rw [lstd_eq, Submodule.span_le]
      rintro _ ⟨⟨v, β⟩, rfl⟩
      show crystallineComparison.psi (σ * gen f R (v, β)) = 1
      rw [hgen]
      obtain ⟨a, b, hab⟩ := h v
      have h2 : σ v * (2 * (R : ℂ)) = (a : ℂ) + (b : ℂ) * Complex.I := by
        rw [hab]; field_simp
      have hre : 2 * R * (σ v).re = a := by
        have := congrArg Complex.re h2
        simp [Complex.mul_re] at this; linarith
      have him : 2 * R * (σ v).im = b := by
        have := congrArg Complex.im h2
        simp [Complex.mul_im] at this; linarith
      cases β
      · exact ⟨a, by simpa using hre⟩
      · exact ⟨-b, by simp [him]⟩
    exact hle hz
end Formalism.FourierDecayAlt.P.PBC.Lat
