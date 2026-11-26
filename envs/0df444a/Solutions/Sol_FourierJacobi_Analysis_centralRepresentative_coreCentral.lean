-- Prove2me | solution 1 for FourierJacobi.Analysis.centralRepresentative_coreCentral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:04.856019+00:00
-- url     : https://prove2.me/submissions/c23effb6-079a-4d96-8ee4-20c5ff3d62a4

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Measure_canonical_uniformizer_zpow
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_nonnegative_iff
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Analysis.coreCentral_one
attribute [local simp] FourierJacobi.Analysis.coreCentral_two
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero
attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (π : Kˣ)
    (hπ : localFieldValuation K (π:K) = 1) (r : Fin 3) :
    CentralRepresentative K (r.val:ℤ) (coreCentral K π r) := by
  by_cases hr : r=0
  · subst r
    exact Or.inl ⟨rfl, coreCentral_zero K π⟩
  · have hr' : (r.val:ℤ) ≠ 0 := by
      intro he
      apply hr
      apply Fin.ext
      change r.val = 0
      exact Int.ofNat_eq_zero.mp he
    have hmem : (π:K) ∈ 𝒪[K] :=
      (localFieldValuation_nonnegative_iff K (π:K)).mp (by rw [hπ]; norm_num)
    let πo : 𝒪[K] := ⟨(π:K),hmem⟩
    have hv := FourierJacobi.Measure.canonical_uniformizer_zpow K πo hπ (-(r.val:ℤ))
    exact Or.inr ⟨hr', by simpa only [coreCentral, hr, if_false] using hv⟩
end FourierJacobi.Analysis
