-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:11.717597+00:00
-- url     : https://prove2.me/submissions/a378bdd6-f562-40cb-871d-acbfc19229f5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_loc_dual_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_loc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : LocDual := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar L hL
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ p : Ideal R, loc (K := K) p (dual h L) = dualAt h p L := fun p =>
    le_antisymm (locDual_loc_dual_le h p L) (locDual_dualAt_le h hstar p L hL)
  have key2 : ∀ p : Ideal R, dualAt h p (loc (K := K) p L) = dualAt h p L :=
    fun p => locDual_dualAt_loc h hinj hstar p L
  refine ⟨fun p _ => ⟨key p, key2 p⟩, ?_⟩
  unfold IsUnimodular IsUnimodularAt
  constructor
  · intro hu p _
    rw [key2, ← key, hu]
  · intro H
    have H' : ∀ p : Ideal R, p.IsMaximal → loc (K := K) p (dual h L) = loc (K := K) p L := by
      intro p hp
      rw [key, ← key2]
      exact H p hp

    have avoid : ∀ p : Ideal R, p.IsPrime → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
      intro p hp s hs
      unfold hcompl at hs
      induction hs using Submonoid.closure_induction with
      | mem s hs => exact hs.1
      | one => exact (Ideal.ne_top_iff_one p).mp hp.ne_top
      | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb

    have incl : ∀ M N : Submodule R V,
        (∀ p : Ideal R, p.IsMaximal → loc (K := K) p M = loc (K := K) p N) → N ≤ M := by
      intro M N hMN x hx
      by_contra hxM
      let I : Ideal R := M.comap (LinearMap.toSpanSingleton R V x)
      have hI : I ≠ ⊤ := by
        intro hI
        apply hxM
        have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
        simpa [I] using h1
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
      have hxN : x ∈ loc (K := K) m N := by
        show ∃ s ∈ hcompl (K := K) m, s • x ∈ N
        exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx⟩
      rw [← hMN m hm] at hxN
      obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) m, s • x ∈ M := hxN
      exact avoid m hm.isPrime s hs (hIm (Submodule.mem_comap.mpr (by simpa using hsx)))
    exact le_antisymm (incl _ _ (fun p hp => (H' p hp).symm)) (incl _ _ H')
end Formalism.HermitianLatticesTheory
