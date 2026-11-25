-- Prove2me | solution 1 for Formalism.DivisionValues.dual_lattice_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:44.506374+00:00
-- url     : https://prove2.me/submissions/120e3af7-94e0-487d-a728-b0326053b0ed

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DualMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Theorems.Thm_Formalism_HN_dual_polygon_identity
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_Formalism_HN_size_maximal_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : DualMu := by
  intro K _ _ _ _ D hD X hX R hR
  have hFG : R.FG := hR.fg
  have hsp : Submodule.span K (R : Set (Fin D → K)) = ⊤ := hR.2
  obtain ⟨hdFG, hdsp, -, hsize, -⟩ :=
    Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG hsp
  have hdX : ∀ v, IsUnit (Formalism.HN.dualFrame X v).det := by
    intro v
    apply Matrix.isUnit_nonsing_inv_det
    rw [Matrix.det_transpose]
    exact hX v
  have hne : Formalism.HN.dualLat R ≠ ⊥ := by
    intro h
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hdsp
    have hmem : (Pi.basisFun K (Fin D)).dualBasis ⟨0, hD⟩ ∈ (⊤ : Submodule K _) := Submodule.mem_top
    rw [← hdsp, Submodule.mem_bot] at hmem
    exact (Pi.basisFun K (Fin D)).dualBasis.ne_zero _ hmem
  have hmu := (Formalism.HN.size_maximal_slope K (Module.Dual K (Fin D → K)) (Fin D) (Pi.basisFun K (Fin D)).dualBasis
    (Formalism.HN.dualFrame X) hdX (Formalism.HN.dualLat R) hdFG hne).2.1
  have hht := (Formalism.HN.place_lattice_structure K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG).2.2
  have hrk : Formalism.HN.rkK R = D := by
    unfold Formalism.HN.rkK
    erw [hsp]
    simp
  have hfr := Formalism.HN.sizeMu_finrank_eq K
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have h0 : 0 < Module.finrank ℚ K := Module.finrank_pos
    have : 0 < Formalism.HN.nPl K := by omega
    exact_mod_cast this
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [hmu, hsize, Real.log_inv, Formalism.HN.size, Real.log_rpow hht, hrk]
  unfold Formalism.DivisionValues.lcv
  rw [hfr]
  push_cast
  field_simp
end Formalism.DivisionValues
