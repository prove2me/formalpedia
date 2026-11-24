-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_minimal_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:44.06514+00:00
-- url     : https://prove2.me/submissions/5908f23f-6692-4bba-9ada-79f5f94baf1b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_inj
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_artinian
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_idem_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]
variable (P)
include P
namespace Formalism.L2.Pj.CompSplitPfC
theorem _root_.solution {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by
  by_contra hne
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors P)
  have hP1 : P1.IsPrime := Ideal.minimalPrimes_isPrime h1
  have hP2 : P2.IsPrime := Ideal.minimalPrimes_isPrime h2
  have hM : ∀ I ∈ minimalPrimes S, Disjoint (M : Set S) I := by
    intro I hI
    refine Set.disjoint_left.2 fun m hm hmI => ?_
    have hnzd : m ∈ nonZeroDivisors S := by
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => cspC_inj (P := P) ?_
      have hu := IsLocalization.map_units (S ⊗[P] FractionRing P) (⟨m, hm⟩ : M)
      have h0 : algebraMap S (S ⊗[P] FractionRing P) x * algebraMap S (S ⊗[P] FractionRing P) m = 0 := by
        rw [← map_mul, hx, map_zero]
      rw [map_zero]
      exact (hu.mul_left_eq_zero).1 h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hI) hmI hnzd
  let Q1 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P1
  let Q2 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P2
  have hQ1 : Q1.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P1 hP1 (hM P1 h1)
  have hQ2 : Q2.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P2 hP2 (hM P2 h2)
  have hc1 : Q1.comap (algebraMap S (S ⊗[P] FractionRing P)) = P1 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP1 (hM P1 h1)
  have hc2 : Q2.comap (algebraMap S (S ⊗[P] FractionRing P)) = P2 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP2 (hM P2 h2)
  have hQne : Q1 ≠ Q2 := fun e => hne (by rw [← hc1, ← hc2, e])
  have := cspC_artinian (P := P) (S := S)
  obtain ⟨r, hr2, hrid, hrall⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne Q2
  have hr1 : r ∈ Q1 := hrall Q1 hQ1 hQne
  obtain ⟨s, hs⟩ := cspC_idem_of (P := P) hrid
  have hs1 : s ∈ P1 := by rw [← hc1, Ideal.mem_comap, hs]; exact hr1
  have hs2 : s ∉ P2 := by rw [← hc2, Ideal.mem_comap, hs]; exact hr2
  have hsid : s * s = s := cspC_inj (P := P) (by rw [map_mul, hs, hrid.eq])
  have h0 : (1 - s) * s ∈ P2 := by
    rw [sub_mul, one_mul, hsid, sub_self]
    exact P2.zero_mem
  have h1s : 1 - s ∈ P2 := (hP2.mem_or_mem h0).resolve_right hs2
  have : (1 : S) ∈ q := by
    have := q.add_mem (hq2 h1s) (hq1 hs1)
    rwa [sub_add_cancel] at this
  exact hq.ne_top ((Ideal.eq_top_iff_one _).2 this)
end Formalism.L2.Pj.CompSplitPfC
