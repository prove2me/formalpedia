-- Prove2me | solution 1 for Formalism.DivisionValues.shift_idealSmul_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:37.53116+00:00
-- url     : https://prove2.me/submissions/c5f9beff-d6e5-401d-91b9-8d269cf4f8a7

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
import Theorems.Thm_Formalism_DivisionValues_shift_smulLat_eq_map
import Theorems.Thm_Formalism_DivisionValues_shift_mem_smulLat
import Theorems.Thm_Formalism_DivisionValues_shift_coe_ne_zero
import Theorems.Thm_Formalism_DivisionValues_shift_smulLat_lattice

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (N : Submodule (𝓞 K) (Fin d → K)) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) := by
  have hNfg : N.FG := Submodule.IsLattice.fg (self := hN)
  obtain ⟨c, hc, hcI⟩ := I.isFractional
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : (c : K) ≠ 0 := shift_coe_ne_zero hc0
  constructor
  · have hle : smulLat (c : K) (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) ≤ N := by
      unfold smulLat Formalism.HermitianLatticesTheory.idealSmul
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨b, hb, x, hx, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := hcI b hb
      show (c : K) • (b • x) ∈ N
      have e : (c : K) • (b • x) = y • x := by
        rw [smul_smul]
        have : (c : K) * b = (y : K) := by
          rw [show (y : K) = algebraMap (𝓞 K) K y from rfl, hy]
          rfl
        rw [this]
        rfl
      rw [e]
      exact N.smul_mem y hx
    have hnoe : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hNfg
    have hfg : (smulLat (c : K) (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N)).FG :=
      isNoetherian_submodule.mp hnoe _ hle
    rw [shift_smulLat_eq_map _ hcK] at hfg
    exact Submodule.fg_of_fg_map_injective _ (shiftEquiv d (c : K) hcK).injective hfg
  · obtain ⟨b, hb, hb0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
    have hbK : (b : K) ≠ 0 := shift_coe_ne_zero hb
    have hle : smulLat (b : K) N ≤ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (shift_mem_smulLat _ N z).mp hz
      exact Submodule.subset_span ⟨_, hb0, x, hx, rfl⟩
    have h1 := Submodule.IsLattice.span_eq_top (self := shift_smulLat_lattice (b : K) hbK N hN)
    rw [eq_top_iff, ← h1]
    exact Submodule.span_mono hle
end Formalism.DivisionValues
