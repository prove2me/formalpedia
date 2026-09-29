-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/89db1fe0-1d27-5e6e-86fa-f670569d0b2c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_linearPart_varpi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (ψ : Zp2 q → k) (g g' : MvPowerSeries (Fin 2) k)
    (hg0 : MvPowerSeries.constantCoeff g = 0) (hg0' : MvPowerSeries.constantCoeff g' = 0)
    (hgP : X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l)))))
    (hgP' : X₀.F.addCoboundary g' ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l)))))
    (hgT : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi)  := by
  by_cases hsmooth : ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
  · exact CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_linearPart_varpi
      X₀ hsmooth.1 hsmooth.2 ψ g g' hg0 hg0' hgP hgP' hgT hgT'
  · exact CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
      X₀ hsmooth ψ g g' hg0 hg0' hgP hgP' hgT hgT'

end S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem (solution)
