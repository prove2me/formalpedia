-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasHeight_four_of_basis_cartierModule_of_X_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9be8233a-cb37-5efc-be3d-6dd549d578ee

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
import Theorems.Thm_MvFormalGroup_Hom_exists_finrank_quotient_span_range_eq_pow_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_basis_cartierModule_of_X_pow_mem_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (X : CerednikDrinfeld.FormalODModule p k)
    (b : Module.Basis (Fin 4) (WittVector p k) (MvFormalGroup.CartierModule p X.F))
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ N ∈
      Ideal.span (Set.range (X.act (p : CerednikDrinfeld.Zp2 p)))) :
    X.HasHeight 4 := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (X.act (p : Zp2 p) i) = 0 := (X.isLawHom_act _).1
  obtain ⟨d, hd⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
      (X.act (p : Zp2 p)) hφ0 hN
  obtain ⟨hfin, hproj, hfib⟩ := hd
  have hfk : Module.finrank k (FormalODModule.KerAlgebra (X.act (p : Zp2 p))) = d := by
    have hmap : (X.act (p : Zp2 p)).map (RingHom.id k) = X.act (p : Zp2 p) := by
      funext i
      simp [Series.map]
    have h1 := hfib k (RingHom.id k)
    rwa [hmap] at h1
  haveI : X.F.IsComm := X.isComm
  obtain ⟨h, hh⟩ :=
    MvFormalGroup.Hom.exists_finrank_quotient_span_range_eq_pow_of_finite p X.F X.F
      (X.actEnd (p : Zp2 p)) (by simp only [FormalODModule.actEnd_toPowerSeries] at hfin ⊢; exact hfin)
  have hdeg : Module.finrank k
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X.F.nthSeries p))) = p ^ h := by
    rw [← X.act_natCast p]
    simp only [FormalODModule.actEnd_toPowerSeries] at hh
    exact hh
  have h4 : h = 4 :=
    CerednikDrinfeld.FormalODModule.eq_four_of_basis_cartierModule_of_finrank_eq_pow p X b h hdeg
  have hd4 : d = p ^ 4 := by
    rw [← hfk, ← h4, ← hdeg, ← X.act_natCast p]
  unfold FormalODModule.HasHeight
  rw [← hd4]
  exact ⟨hfin, hproj, hfib⟩

end S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_basis_cartierModule_of_X_pow_mem_span
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_basis_cartierModule_of_X_pow_mem_span (solution)
