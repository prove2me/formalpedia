-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.isOpen_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:10.397798+00:00
-- url     : https://prove2.me/submissions/02a3b20c-1ab7-4de1-923c-af082d7877d1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.F
namespace PeriodLatticeBasisLemmas
private theorem mem_lattice_iff_exists_int_comb' (L : PeriodPair) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ = x := by
  exact L.mem_lattice
private theorem periodPair_basis_zero_eq_omega_one (L : PeriodPair) : L.basis 0 = L.ω₁ := by
  exact L.basis_zero
private theorem periodPair_basis_one_eq_omega_two (L : PeriodPair) : L.basis 1 = L.ω₂ := by
  exact L.basis_one
private theorem basis_equivFun_real_comb_periods (L : PeriodPair) (s t : ℝ) :
    L.basis.equivFun ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = ![s, t] := by
  have e : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = L.basis.equivFun.symm ![s, t] := by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two]
    simp [Complex.real_smul]
  rw [e, LinearEquiv.apply_symm_apply]
private theorem lattice_eq_iInter_preimage_int_coords (L : PeriodPair) :
    (L.lattice : Set ℂ) = ⋂ i : Fin 2, (fun x => L.basis.equivFun x i) ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro hx i
    obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
    have h : L.basis.equivFun ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = ![(m : ℝ), (n : ℝ)] := by
      exact_mod_cast basis_equivFun_real_comb_periods L m n
    rw [h]
    fin_cases i
    · exact ⟨m, rfl⟩
    · exact ⟨n, rfl⟩
  · intro h
    obtain ⟨m, hm⟩ := h 0
    obtain ⟨n, hn⟩ := h 1
    refine (mem_lattice_iff_exists_int_comb' L).mpr ⟨m, n, ?_⟩
    have hs := L.basis.sum_equivFun x
    rw [Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two, ← hm, ← hn] at hs
    rw [← hs]
    simp [Complex.real_smul]
private theorem isClosed_periodPair_lattice (L : PeriodPair) : IsClosed (L.lattice : Set ℂ) := by
  rw [lattice_eq_iInter_preimage_int_coords]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun x : ℂ => L.basis.equivFun x i :=
    (continuous_apply i).comp (LinearMap.continuous_of_finiteDimensional L.basis.equivFun.toLinearMap)
  exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage hc
end PeriodLatticeBasisLemmas
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) :=
  (isClosed_periodPair_lattice L).isOpen_compl
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
