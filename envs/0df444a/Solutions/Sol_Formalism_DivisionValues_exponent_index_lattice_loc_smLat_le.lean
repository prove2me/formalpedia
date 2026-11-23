-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.loc_smLat_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:17.936224+00:00
-- url     : https://prove2.me/submissions/a47b7bea-72ba-454a-83da-a83decf4232b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_smLat

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
theorem _root_.solution {D : ℕ} (a : K) (p : Ideal (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin D → K)}
    (h : Formalism.HermitianLatticesTheory.loc (K := K) p L ≤ Formalism.HermitianLatticesTheory.loc (K := K) p L') :
    Formalism.HermitianLatticesTheory.loc (K := K) p (smLat a L) ≤ Formalism.HermitianLatticesTheory.loc (K := K) p (smLat a L') := by
  intro x hx
  have hx' : ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s • x ∈ smLat a L := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨y, hy, hya⟩ := (mem_smLat a L _).mp hsx
  show ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, t • x ∈ smLat a L'
  by_cases ha : a = 0
  · refine ⟨s, hs, ?_⟩
    rw [← hya, ha, zero_smul]
    exact Submodule.zero_mem _
  · have hyloc : a⁻¹ • x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
      show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s • a⁻¹ • x ∈ L
      refine ⟨s, hs, ?_⟩
      rw [smul_comm, ← hya, smul_smul, inv_mul_cancel₀ ha, one_smul]
      exact hy
    have hty : ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, t • a⁻¹ • x ∈ L' := h hyloc
    obtain ⟨t, ht, htL⟩ := hty
    refine ⟨t, ht, (mem_smLat a L' _).mpr ⟨t • a⁻¹ • x, htL, ?_⟩⟩
    rw [smul_comm a t, smul_smul, mul_inv_cancel₀ ha, one_smul]
end Formalism.DivisionValues.exponent_index_lattice
