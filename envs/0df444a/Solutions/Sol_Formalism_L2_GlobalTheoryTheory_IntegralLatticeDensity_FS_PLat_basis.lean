-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:38.321899+00:00
-- url     : https://prove2.me/submissions/00c603d1-854f-4950-864f-10d86c8f80d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_zero_left
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_fam
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_linInd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace PLat
theorem _root_.solution (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = finrank K V) :
    ∃ (b : Basis ι K V) (n : ι → ℕ), Good h L p b n := by
  have H := P.herm
  obtain ⟨v, n, gL, gn, gp, go⟩ := P.fam (finrank K V) le_rfl
  let e : ι ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hι
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i e0
    have h1 := gn i
    rw [e0, H.zero_left] at h1
    have : n i = 0 := by exact_mod_cast h1.symm
    exact gp i (this ▸ dvd_zero p)
  have hv' : ∀ i j : ι, i ≠ j → h (v (e i)) (v (e j)) = 0 := fun i j hij => go _ _ (fun e' => hij (e.injective e'))
  have hli : LinearIndependent K (fun i => v (e i)) := H.linInd _ (fun i => hv0 _) hv'
  have hsp := hli.span_eq_top_of_card_eq_finrank' hι
  refine ⟨Basis.mk hli (le_of_eq hsp.symm), fun i => n (e i), ?_, ?_, fun i => gp _, ?_⟩
  · intro i; rw [Basis.mk_apply]; exact gL _
  · intro i; rw [Basis.mk_apply]; exact gn _
  · intro i j hij; rw [Basis.mk_apply, Basis.mk_apply]; exact hv' i j hij
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
