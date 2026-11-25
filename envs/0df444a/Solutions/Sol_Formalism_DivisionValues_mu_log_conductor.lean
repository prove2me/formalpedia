-- Prove2me | solution 1 for Formalism.DivisionValues.mu_log_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:24.126398+00:00
-- url     : https://prove2.me/submissions/0fa23e8a-0c3c-46db-a1a5-b75bc44ac23b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
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
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : MuLcv := by
  intro K _ _ _ _ d hd X hX N hN
  have hfg : N.FG := Submodule.IsLattice.fg (self := hN)
  have hspan : Submodule.span K (N : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hN)
  have hne : N ≠ ⊥ := by
    intro h
    have h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin d → K))) : Set (Fin d → K)) = ⊥ := by
      simp
    rw [h, h2] at hspan
    have h3 := congrArg (fun U : Submodule K (Fin d → K) => finrank K U) hspan
    simp only [finrank_bot, finrank_top, finrank_fin_fun] at h3
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d)
    (Pi.basisFun K (Fin d)) X hX N hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X N :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX N hfg).2.2
  have hrk : Formalism.HN.rkK N = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, lcv, hn]
  field_simp
end Formalism.DivisionValues
