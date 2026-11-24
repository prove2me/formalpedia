-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.lidx_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.768803+00:00
-- url     : https://prove2.me/submissions/ea86acd6-d944-4fcc-b30f-4451dde6c394

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
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


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
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (p : Ideal R) [p.IsPrime] (A B C : Submodule R V)
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    Formalism.HermitianLatticesTheory.lidx p A C = Formalism.HermitianLatticesTheory.lidx p A B + Formalism.HermitianLatticesTheory.lidx p B C := by
  have hfin : ∀ X Y : Submodule R V, X.FG → Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ p X) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ p Y).comap (Formalism.HermitianLatticesTheory.localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨d, hd, hdY⟩ :=
      Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (Formalism.HermitianLatticesTheory.indexBasic_finLen p X Y hX hd hdY)
  have hAt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) A
    (Submodule.IsLattice.span_eq_top (self := hA))
  have hBt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B
    (Submodule.IsLattice.span_eq_top (self := hB))
  have hCt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) C
    (Submodule.IsLattice.span_eq_top (self := hC))
  have hAfg : A.FG := Submodule.IsLattice.fg (self := hA)
  have hBfg : B.FG := Submodule.IsLattice.fg (self := hB)
  have hCfg : C.FG := Submodule.IsLattice.fg (self := hC)
  have hDt : Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
    rw [Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hAt, hBt, hCt]
    simp
  have hAD := hfin A _ hAfg hDt
  have hBD := hfin B _ hBfg hDt
  have hCD := hfin C _ hCfg hDt
  rw [Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      inf_le_right hAD hCD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right)
      inf_le_right hBD hCD]
  ring
end Formalism.DivisionValues.StepBAux
