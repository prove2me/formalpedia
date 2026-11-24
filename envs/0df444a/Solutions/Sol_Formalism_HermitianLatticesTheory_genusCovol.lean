-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:21.917865+00:00
-- url     : https://prove2.me/submissions/37a3d8d8-99a4-46a0-a41c-6518dbba9377

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_lemmaS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_gmap_inf
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_sq
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_local
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_addData
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_trace_int
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusScale
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : GenusCovol := by
  intro K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L M hL hM _ _ _ _
  classical
  have hMl : Submodule.IsLattice K M := hM.1
  obtain ⟨d, hd0, hd⟩ := genusScale K V h hs L hL
  have hLgen : L ∈ genus h L := ⟨hL, fun p _ => ⟨1, (isom h).one_mem, genusBasic_gmap_one _⟩⟩
  have hDmem : ∀ A ∈ genus h L, ∀ x ∈ A, d • x ∈ genusCovol_tdual h A := by
    intro A hA x hx y hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hd A hA y hy x hx)
    obtain ⟨z, hz⟩ := genusCovolBound_trace_int r
    refine ⟨z, ?_⟩
    rw [map_nsmul, nsmul_eq_mul, ← hz, hr]
  obtain ⟨hL1, hL2, hLsq⟩ := genusCovol_sq h hpos N ι hι L d hd0 (hDmem L hLgen)
  obtain ⟨hM1, hM2, hMsq⟩ := genusCovol_sq h hpos N ι hι M d hd0 (hDmem M hM)
  have hloc : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], ∃ g : V ≃ₗ[K] V,
      gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧
      gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
        locS P.primeCompl (genusCovol_tdual h M) := by
    intro P hP
    obtain ⟨g, hg, hgL⟩ := hM.2 P hP
    exact ⟨g, genusCovol_local h L M hL.fg hMl.fg P g hg hgL⟩
  have hinf : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal] (g : V ≃ₗ[K] V),
      gmap g (locS P.primeCompl L) = locS P.primeCompl M →
      gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
        locS P.primeCompl (genusCovol_tdual h M) →
      gmap g (locS P.primeCompl (L ⊓ genusCovol_tdual h L)) =
        locS P.primeCompl (M ⊓ genusCovol_tdual h M) := by
    intro P _ g e1 e2
    rw [locBasic_locS_inf, locBasic_locS_inf, genusCovol_gmap_inf, e1, e2]
  have eA := genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) L (M ⊓ genusCovol_tdual h M) M
    inf_le_left inf_le_left rfl hL1 hM1 (by
      intro P _
      obtain ⟨g, e1, e2⟩ := hloc P
      exact ⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2),
        genusCovol_addData g _ _ e1⟩)
  have eB := genusCovol_lemmaS _ (L ⊓ genusCovol_tdual h L) (genusCovol_tdual h L)
    (M ⊓ genusCovol_tdual h M) (genusCovol_tdual h M)
    inf_le_right inf_le_right rfl hL2 hM2 (by
      intro P _
      obtain ⟨g, e1, e2⟩ := hloc P
      exact ⟨_, g.injective, genusCovol_addData g _ _ (hinf P g e1 e2),
        genusCovol_addData g _ _ e2⟩)
  rw [eA, eB, ← hLsq] at hMsq
  have hr0 : (0 : ℝ) < ((L ⊓ genusCovol_tdual h L).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hL1
  have hsq := mul_right_cancel₀ hr0.ne' hMsq
  exact (pow_left_inj₀ (ZLattice.covolume_pos (zmap ι M)).le (ZLattice.covolume_pos (zmap ι L)).le
    two_ne_zero).mp hsq
end Formalism.HermitianLatticesTheory
