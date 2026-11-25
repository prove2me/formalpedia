-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:55.583073+00:00
-- url     : https://prove2.me/submissions/5814b62f-2807-4c74-ac9f-6d3352da4446

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
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_smLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_idx_smLat

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
namespace Formalism.DivisionValues
theorem _root_.solution : ExpIndexLoc := by
  intro K _ _ _ D A B hA hB w a ha hAB
  have ha' : (a : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hC : Submodule.IsLattice K (smLat (a : K) A) := map_isLattice (sm D (a : K)) (sm_surj D ha') A hA
  obtain ⟨-, hsum, -⟩ := idxB w A (smLat (a : K) A) B hA hC hB
  rw [hsum, idx_smLat w A hA ha']
  have htop : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A ⊓ B)).comap
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)).subtype = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    obtain ⟨s, hs, hsx⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • x ∈ smLat (a : K) A := hx
    obtain ⟨y, hy, hyx⟩ := (mem_smLat (a : K) A _).mp hsx
    obtain ⟨t, ht, htB⟩ : ∃ t ∈ w.asIdeal.primeCompl, t • a • y ∈ B := hAB y hy
    show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ smLat (a : K) A ⊓ B
    refine ⟨t * s, w.asIdeal.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact Submodule.smul_mem _ t hsx
    · rw [mul_smul, ← hyx, show ((a : K)) • y = a • y from algebraMap_smul K a y]
      exact htB
  have hz : Formalism.HermitianLatticesTheory.locLen w.asIdeal (smLat (a : K) A) (smLat (a : K) A ⊓ B) = 0 := by
    unfold Formalism.HermitianLatticesTheory.locLen
    have hsub : Subsingleton (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)) ⧸
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A ⊓ B)).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)).subtype) :=
    ⟨fun u v => Submodule.Quotient.induction_on _ u (fun x => Submodule.Quotient.induction_on _ v (fun y =>
      (Submodule.Quotient.eq _).mpr (by rw [htop]; trivial)))⟩
    rw [Module.length_eq_zero_iff.mpr hsub]
    rfl
  have hle : idx w (smLat (a : K) A) B ≤ 0 := by
    unfold idx Formalism.HermitianLatticesTheory.lidx
    rw [hz]
    simp
  linarith
end Formalism.DivisionValues
