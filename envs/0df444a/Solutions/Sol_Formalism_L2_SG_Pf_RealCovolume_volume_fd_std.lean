-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.volume_fd_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:30.461799+00:00
-- url     : https://prove2.me/submissions/05f04b51-dfa2-4b4e-835c-76f05e8b02dd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
import Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_reCo_apply
import Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_bstd_repr
import Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_volume_box
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped Matrix
namespace Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
private theorem mem_fundamentalDomain_reindex_bstd_iff {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) (m : ι → κ → ℂ) :
    m ∈ ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) ↔
      ∀ p, reCo m p ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ZSpan.mem_fundamentalDomain]
  first
  | simp only [Module.Basis.repr_reindex_apply, Equiv.symm_symm, bstd_repr]
  | simp only [Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, bstd_repr]
  constructor
  · intro h p
    have := h (e.symm p)
    rwa [Equiv.apply_symm_apply] at this
  · intro h j
    exact h (e j)
end Formalism.L2.SG.Pf.RealCovolume
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace Formalism.L2.SG.Pf.RealCovolume
theorem _root_.solution {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) :
    volume (ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm)) = 1 := by
  have hset : ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC := by
    ext m
    rw [mem_fundamentalDomain_reindex_bstd_iff]
    constructor
    · intro h
      rw [Set.mem_pi]
      intro i _
      rw [Set.mem_pi]
      intro c _
      show (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1
      exact ⟨by simpa [reCo_apply] using h (i, c, 0), by simpa [reCo_apply] using h (i, c, 1)⟩
    · intro h p
      obtain ⟨i, c, t⟩ := p
      have hi := Set.mem_pi.1 h i (Set.mem_univ _)
      have hic' := Set.mem_pi.1 hi c (Set.mem_univ _)
      have hic : (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1 := hic'
      rw [reCo_apply]
      fin_cases t
      · simpa using hic.1
      · simpa using hic.2
  rw [hset, volume_box]
end Formalism.L2.SG.Pf.RealCovolume
