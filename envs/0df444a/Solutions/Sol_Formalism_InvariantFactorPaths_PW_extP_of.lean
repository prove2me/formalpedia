-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.extP_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:45.873525+00:00
-- url     : https://prove2.me/submissions/275b5b52-a698-4a2b-874c-67768686131c

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isHW_of_mem_gSall
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_mem_lowIm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_iSup_isoC_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lowIm_le_lowC
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lowC_le_perpV
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_comp_right
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_comp_comm_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_eq_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_nondeg
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_le_isoC
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_projection_lattice_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_typeProj_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hI : IntP) : ExtP := by
  intro p _ N r LL ρ j _ la
  set Cs : Finset (Fin r) := univ.erase ρ with hCs
  have hcard : Cs.card = r - 1 := by
    rw [hCs, Finset.card_erase_of_mem (Finset.mem_univ ρ), Finset.card_univ, Fintype.card_fin]
  set T : Set (Fin r → ℤ) := {la' : Fin r → ℤ | ∀ c ∈ Cs, la' c = la c} with hT
  have hsat : CsSaturated Cs T := by
    intro a b hab
    constructor
    · intro h c hc; rw [← hab c hc]; exact h c hc
    · intro h c hc; rw [hab c hc]; exact h c hc
  obtain ⟨PT, hPT, hadj⟩ := projection_lattice_holds p N r LL j Cs T hsat
  have hidem : ∀ x, PT (PT x) = PT x := fun x => congrArg (fun f => f x) hPT.1
  have hrange : LinearMap.range PT = IsoC p LL j Cs la := by
    rw [hPT.2.1]; exact iSup_isoC_eq LL j Cs la
  have hker := hPT.2.2
  set Gu := GAe p LL j (enumC (univ : Finset (Fin r))) with hGu
  set lu : Fin (univ : Finset (Fin r)).card → ℤ := la ∘ enumC univ with hlu
  set G := GAe p LL j (enumC Cs) with hG
  have hwt : ∀ x, x ∈ WtSpC p LL j univ la ↔ Gu.IsWt lu x := fun x => wtSpC_iff LL j univ la x

  have hcomm : ∀ x, PT (Gu.comp lu x) = Gu.comp lu (PT x) := by
    intro x
    refine Formalism.CountingSumsFrames.GlX.comp_comm_of Gu (W := ⊤) (fun _ _ _ => Submodule.mem_top) PT ?_ x Submodule.mem_top lu
    intro y _ c
    exact congrArg (fun f => f y)
      (typeProj_comm LL j Cs T PT hPT (glAct p LL j (enumC univ c) (enumC univ c)) (isoC_diag LL j Cs _))
  have hfix : ∀ x ∈ IsoC p LL j Cs la, PT x = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hidem y
  have hP_wt : ∀ x ∈ WtSpC p LL j univ la, (PT ∘ₗ Gu.comp lu) x = PT x := by
    intro x hx
    rw [LinearMap.comp_apply, (hwt x).mp hx]
  have hmem : ∀ x, (PT ∘ₗ Gu.comp lu) x ∈ HWC p LL j Cs la ⊓ WtSpC p LL j univ la := by
    intro x
    have h1 : (PT ∘ₗ Gu.comp lu) x ∈ IsoC p LL j Cs la := by
      rw [← hrange]; exact LinearMap.mem_range_self _ _
    have h2 : (PT ∘ₗ Gu.comp lu) x ∈ WtSpC p LL j univ la := by
      rw [LinearMap.comp_apply, hcomm, hwt]
      exact Gu.isWt_comp lu _
    refine Submodule.mem_inf.mpr ⟨?_, h2⟩
    rw [hwc_iff]
    rw [isoC_eq] at h1
    exact isHW_of_mem_gSall G h1 ((wtSpC_iff LL j Cs la _).mp (wtSpC_mono LL j (Finset.subset_univ Cs) la h2))
  refine ⟨PT ∘ₗ Gu.comp lu, ?_, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hP_wt _ (hmem x).2]
    exact hfix _ (hwc_le_isoC LL j Cs la (hmem x).1)
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hmem x
    · intro h hh
      refine ⟨h, ?_⟩
      rw [hP_wt h hh.2]
      exact hfix h (hwc_le_isoC LL j Cs la hh.1)
  · show LinearMap.ker (PT ∘ₗ Gu.comp lu) ⊓ WtSpC p LL j univ la = lowC p LL j Cs ⊓ WtSpC p LL j univ la
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hP_wt x hx2, ← LinearMap.mem_ker, hker] at hx1
      have hle : (⨆ (mu : Fin r → ℤ) (_ : mu ∉ T), IsoC p LL j Cs mu) ≤
          (lowC p LL j Cs).comap (G.comp (la ∘ enumC Cs)) := by
        refine iSup₂_le fun mu hmu => ?_
        intro z hz
        rw [isoC_eq] at hz
        rw [Submodule.mem_comap]
        refine lowIm_le_lowC LL j Cs (comp_mem_lowIm G ?_ hz)
        intro h
        exact hmu ((comp_eq_iff Cs mu la).mp h.symm)
      have h3 := hle hx1
      rw [Submodule.mem_comap] at h3
      have h4 : G.comp (la ∘ enumC Cs) x = x :=
        (wtSpC_iff LL j Cs la x).mp (wtSpC_mono LL j (Finset.subset_univ Cs) la hx2)
      rwa [h4] at h3
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hP_wt x hx2]
      refine fock_nondeg _ fun y => ?_
      rw [hadj, fock_comp_right LL j (enumC univ) ((hwt x).mp hx2) (PT y)]
      have h5 : Gu.comp lu (PT y) ∈ HWC p LL j Cs la := by
        rw [← hcomm]; exact (hmem y).1
      exact lowC_le_perpV LL j Cs la h5 hx1
  · intro F F' hF hF'
    rw [hP_wt F hF, hP_wt F' hF']
    exact hadj F F'
  · intro F hF hFw
    rw [hP_wt F hFw, ← hcard]
    exact hI p N r LL j Cs T PT hsat hPT F hF
end Formalism.InvariantFactorPaths.PW
