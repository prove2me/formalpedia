-- Prove2me | solution 1 for Formalism.HN.saturation_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:46.80314+00:00
-- url     : https://prove2.me/submissions/98b092aa-9c43-4e07-a750-0ba7c86fbec3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Theorems.Thm_Formalism_HN_satBasic_zl_mono
import Theorems.Thm_Formalism_HN_satBasic_zl_bot
import Theorems.Thm_Formalism_F_att_rk_le
import Theorems.Thm_Formalism_F_att_rk_pos
import Theorems.Thm_Formalism_F_covolAntiSameRank
import Theorems.Thm_Formalism_F_covolBasic
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_F_discreteTopology_of_le
import Theorems.Thm_Formalism_HN_exists_smul_mem_of_finrank_eq
import Theorems.Thm_Formalism_HN_satR_mem_zl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : SatBasic := by
  intro R V E _ _ _ _ _ _ ρ L hL
  haveI hLd : DiscreteTopology (zl ρ L) := hL.2
  have hdisc : ∀ N : Submodule R V, N ≤ L → DiscreteTopology (zl ρ N) := fun N h =>
    Formalism.F.discreteTopology_of_le (satBasic_zl_mono ρ h)

  have hrev : ∀ A B : Submodule R V, A ≤ L → B ≤ L → zl ρ B ≤ zl ρ A → B ≤ A := by
    intro A B hAL hBL h y hy
    obtain ⟨z, hz, hzy⟩ := (satR_mem_zl ρ A _).mp (h ((satR_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩))
    have := hL.1 (hAL hz) (hBL hy) hzy
    rw [← this]; exact hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N h
    exact ⟨hL.1.mono (fun x hx => h hx), hdisc N h⟩
  · intro A B hAB hBL
    haveI := hdisc B hBL
    haveI := hdisc A (hAB.trans hBL)
    refine ⟨Formalism.F.att_rk_le (satBasic_zl_mono ρ hAB), fun hr => ?_⟩
    have hc := Formalism.F.covolAntiSameRank E (zl ρ A) (zl ρ B) (hdisc B hBL)
      (satBasic_zl_mono ρ hAB) hr
    have hpB := Formalism.F.covol_pos (zl ρ B)
    show -Real.log (Formalism.F.covol (zl ρ A)) ≤ -Real.log (Formalism.F.covol (zl ρ B))
    have := Real.log_le_log hpB hc
    linarith
  · intro S N hS hSN hNL hr
    haveI := hdisc N hNL
    refine le_antisymm (hrev S N hS.1 hNL ?_) hSN
    intro x hx
    obtain ⟨a, ha, hax⟩ :=
      exists_smul_mem_of_finrank_eq (zl ρ N) (zl ρ S) (satBasic_zl_mono ρ hSN) hr x hx
    refine hS.2.2 x (satBasic_zl_mono ρ hNL hx) ?_
    have hx' : x = (a : ℝ)⁻¹ • ((a : ℝ) • x) := by
      rw [inv_smul_smul₀ (by exact_mod_cast ha)]
    rw [hx']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact hax
  · intro N hNL
    haveI := hdisc N hNL
    constructor
    · intro h0
      have h0' : Formalism.F.rk (zl ρ N) = 0 := h0
      have hb : zl ρ N = ⊥ := by
        by_contra hne
        have := Formalism.F.att_rk_pos hne
        omega
      rw [eq_bot_iff]
      intro y hy
      have hy' : ρ y ∈ zl ρ N := (satR_mem_zl ρ N _).mpr ⟨y, hy, rfl⟩
      rw [hb, Submodule.mem_bot] at hy'
      rw [Submodule.mem_bot]
      exact hL.1 (hNL hy) (Submodule.zero_mem L) (by rw [hy', map_zero])
    · rintro rfl
      show Formalism.F.rk (zl ρ ⊥) = 0
      rw [satBasic_zl_bot ρ]
      simp [Formalism.F.rk]
  · show -Real.log (Formalism.F.covol (zl ρ ⊥)) = 0
    rw [satBasic_zl_bot ρ, (Formalism.F.covolBasic E).1]
    simp
  · refine ⟨bot_le, ?_⟩
    rw [satBasic_zl_bot ρ]
    refine ⟨bot_le, fun x _ hx => ?_⟩
    simpa using hx
  · exact ⟨le_rfl, le_rfl, fun x hx _ => hx⟩
  · intro S hS
    haveI := hdisc S hS.1
    obtain ⟨_, h2, h3⟩ := Formalism.F.degQuot E (zl ρ L) (zl ρ S) hLd hS.2
    refine ⟨?_, ?_, ?_⟩
    · show _ = Formalism.F.rk (zl ρ L) - Formalism.F.rk (zl ρ S)
      omega
    · show Formalism.F.rk (zl ρ S) ≤ Formalism.F.rk (zl ρ L)
      omega
    · show _ = Formalism.F.deg (zl ρ L) - Formalism.F.deg (zl ρ S)
      linarith
end Formalism.HN
