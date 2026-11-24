-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.356883+00:00
-- url     : https://prove2.me/submissions/ba05d283-76bb-4b65-97bf-3fc2537ac50e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_le_of_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_lg
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_sup
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_not_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_hcompl
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le_conj

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
theorem _root_.solution : LocBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ hinj
  unfold loc localization₂
  have hne : ∀ (p : Ideal R), p.IsPrime → ∀ s ∈ hcompl (K := K) p, algebraMap R K s ≠ 0 := by
    intro p hp s hs h0
    haveI := hp
    apply locBasic_hcompl_not_mem (K := K) p s hs
    rw [← map_zero (algebraMap R K)] at h0
    rw [hinj h0]
    exact p.zero_mem
  have hnm : ∀ (p : Ideal R), p.IsMaximal → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
    intro p hp s hs
    haveI := hp.isPrime
    exact locBasic_hcompl_not_mem (K := K) p s hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp L M
    haveI := hp
    exact ⟨locBasic_le_locS _ L, fun h => locBasic_locS_mono _ h, locBasic_locS_idem _ L,
      locBasic_locS_inf _ L M, locBasic_locS_sup (K := K) _ (hne p hp) L M⟩
  · intro L
    apply le_antisymm
    · intro x hx
      simp only [Submodule.mem_iInf] at hx
      exact locBasic_lg (fun p => hcompl (K := K) p) hnm L x hx
    · exact le_iInf₂ fun p _ => locBasic_le_locS _ L
  · intro L M h x hx
    exact locBasic_lg (fun p => hcompl (K := K) p) hnm M x
      (fun p hp => h p hp (locBasic_le_locS _ L hx))
  · intro p _ L
    exact locBasic_locS_le_of_le (locBasic_hcompl_le (K := K) p) L
  · intro hstar p _
    have hc := locBasic_conj_eq hinj hstar p
    haveI hpc : (conjIdeal (K := K) p).IsPrime := by
      rw [hc]
      exact Ideal.comap_isPrime _ _
    refine ⟨hpc, fun L => ?_⟩
    apply le_antisymm
    · exact le_inf (locBasic_locS_le_of_le (locBasic_hcompl_le (K := K) p) L)
        (locBasic_locS_le_of_le (locBasic_hcompl_le_conj hinj hstar p) L)
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).1
      obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).2
      have hs' : s ∉ p := Ideal.mem_primeCompl_iff.mp hs
      have ht' : locBasic_sigma hinj hstar t ∉ p := by
        have h1 := Ideal.mem_primeCompl_iff.mp ht
        rwa [hc, Ideal.mem_comap] at h1
      have key : ∀ u, u • x ∈ L → u ∉ p → locBasic_sigma hinj hstar u ∉ p →
          x ∈ locS (hcompl (K := K) p) L := by
        intro u hux hu1 hu2
        refine locBasic_mem_locS.mpr ⟨u, locBasic_mem_hcompl (K := K) p u hu1 ?_, hux⟩
        rw [hc, Ideal.mem_comap]
        exact hu2
      by_cases h1 : locBasic_sigma hinj hstar s ∈ p
      · by_cases h2 : t ∈ p
        · refine key (s + t) (by rw [add_smul]; exact L.add_mem hsx htx) ?_ ?_
          · intro h
            exact hs' (by simpa using p.sub_mem h h2)
          · rw [map_add]
            intro h
            exact ht' (by simpa using p.sub_mem h h1)
        · exact key t htx h2 ht'
      · exact key s hsx hs' h1
end Formalism.HermitianLatticesTheory
