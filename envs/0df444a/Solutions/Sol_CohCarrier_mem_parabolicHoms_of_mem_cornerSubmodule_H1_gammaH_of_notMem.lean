-- Prove2me | solution 1 for CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/265e138e-c652-5c20-9499-5391c02c97f4

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

namespace CohCarrier p2m_export "CohCarrier" "Gen opFamily hdata Gen.T GammaH H1 heckeT heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one" end CohCarrier
p2m_open_scoped "CohCarrier" in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
open scoped IsMulCommutative in

theorem CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem'
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N H S 𝒪 g * CohCarrier.opFamily N H S 𝒪 h =
        CohCarrier.opFamily N H S 𝒪 h * CohCarrier.opFamily N H S 𝒪 g)
    (θbar : CohCarrier.Gen N S → k)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N])
    (hnot : (⟨(CohCarrier.hdata N H S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
            ((ℓ : ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra) + 1)) ∉ Sp.𝔪 i₀)
    (hstab : ∀ (g : CohCarrier.Gen N S) (ψ : CohCarrier.H1 N H 𝒪),
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 →
        CohCarrier.opFamily N H S 𝒪 g ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪)
    (φ : CohCarrier.H1 N H 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N H 𝒪) (Sp.e i₀)) :
    φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪 := by
  let D := CohCarrier.hdata N H S 𝒪 k hcomm θbar

  have hW : ∀ b ∈ D.opSubalgebra, ∀ ψ : CohCarrier.H1 N H 𝒪,
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 →
        b ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 := by
    intro b hb
    refine Algebra.adjoin_induction (hx := hb) ?_ ?_ ?_ ?_
    · rintro _ ⟨g, rfl⟩ ψ hψ
      exact hstab g ψ hψ
    · intro r ψ hψ
      change (algebraMap 𝒪 (Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) r) ψ ∈ _
      rw [Module.algebraMap_end_apply]
      exact (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪).smul_mem r hψ
    · intro a b _ _ ha hb ψ hψ
      rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (ha ψ hψ) (hb ψ hψ)
    · intro a b _ _ ha hb ψ hψ
      rw [Module.End.mul_apply]
      exact ha _ (hb ψ hψ)

  set x : ↥D.opSubalgebra := ⟨D.op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN), Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
    ((ℓ : ↥D.opSubalgebra) + 1) with hx
  obtain ⟨t, ht⟩ := IharaLemma.exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀)
    (Sp.mem_of_isMaximal_of_ne i₀) hnot

  obtain ⟨v, hv⟩ := hφ
  have hφ' : φ = Sp.e i₀ • v := by rw [← hv]; rfl
  rw [hφ']
  have key : Sp.e i₀ • v = t • (x • (Sp.e i₀ • v)) := by
    rw [← mul_smul, ← mul_smul, ht]
  rw [key]

  show (t : Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) ((x : Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) (Sp.e i₀ • v)) ∈
    ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪
  apply hW _ t.2
  set ψ := Sp.e i₀ • v
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hb := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one N H 𝒪 ψ ℓ hℓ hℓN hℓ1
  have h1 : (x : Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) =
      D.op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) - ((ℓ : Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) + 1) := by rw [hx]; rfl
  have hxψ : (x : Module.End 𝒪 (CohCarrier.H1 N H 𝒪)) ψ = CohCarrier.heckeT N H ℓ 𝒪 ψ - (ℓ + 1) • ψ := by
    rw [h1, LinearMap.sub_apply, LinearMap.add_apply, Module.End.natCast_apply, Module.End.one_apply, add_smul, one_smul]
    rfl
  rw [hxψ]; exact hb

set_option maxHeartbeats 3200000 in
open scoped IsMulCommutative in
theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N H S 𝒪 g * CohCarrier.opFamily N H S 𝒪 h =
        CohCarrier.opFamily N H S 𝒪 h * CohCarrier.opFamily N H S 𝒪 g)
    (θbar : CohCarrier.Gen N S → k)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N])
    (hnot : (⟨(CohCarrier.hdata N H S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
            ((ℓ : ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra) + 1)) ∉ Sp.𝔪 i₀)
    (hstab : ∀ (g : CohCarrier.Gen N S) (ψ : CohCarrier.H1 N H 𝒪),
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 →
        CohCarrier.opFamily N H S 𝒪 g ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪)
    (φ : CohCarrier.H1 N H 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N H 𝒪) (Sp.e i₀)) :
    φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪 :=
  CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem' N H S 𝒪 k hcomm θbar Sp i₀ ℓ hℓ hℓS hℓN hℓ1 hnot hstab φ hφ

end S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem
end P2MW
export P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem (solution)
