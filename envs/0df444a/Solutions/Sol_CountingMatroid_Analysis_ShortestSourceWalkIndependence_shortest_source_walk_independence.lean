-- Prove2me | solution 1 for CountingMatroid.Analysis.ShortestSourceWalkIndependence.shortest_source_walk_independence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:07:07.400982+00:00
-- url     : https://prove2.me/submissions/c7268e85-3750-40ec-941a-ab132d846901

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_walk_suffix_length

namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-! The first-matroid half of shortest-path augmentation. Fundamental circuits
of later outside vertices avoid all earlier removed inside vertices, since such
membership would give a shorter source walk. -/
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open scoped symmDiff



/-- INTERNAL: For a fresh list vertex, symmetric difference performs exactly
one insertion or erasure according to original membership. -/
theorem symmDiff_cons {n : ℕ} (I : Finset (Fin n)) (v : Fin n)
    (p : List (Fin n)) (hv : v ∉ p) :
    I ∆ (v :: p).toFinset =
      if v ∈ I then (I ∆ p.toFinset).erase v else insert v (I ∆ p.toFinset) := by
  classical
  ext w
  by_cases hw : w = v
  · subst w
    by_cases hvi : v ∈ I <;> simp [Finset.mem_symmDiff, hvi, hv]
  · by_cases hvi : v ∈ I <;> simp [Finset.mem_symmDiff, hw, hvi]





end CountingMatroid.Analysis.ShortestSourceWalkIndependence

end
set_option autoImplicit false

/-! The first-matroid half of shortest-path augmentation. Fundamental circuits
of later outside vertices avoid all earlier removed inside vertices, since such
membership would give a shorter source walk. -/
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open scoped symmDiff

/-- INTERNAL: Shortest source walks preserve first-matroid independence.
When the head is inside, reinserting it recovers the independent set just
before that head was removed; this strengthens the induction invariant.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M : Matroid (Fin n))
    (g : ExchangeGraph n) (I : Finset (Fin n)) (hE : M.E = Set.univ)
    (hI : M.Indep (I : Set (Fin n)))
    (hsrc : ∀ v, (g.terminals v).1 = true ↔
      v ∉ I ∧ M.Indep (insert v (I : Set (Fin n))))
    (halt : ∀ u v, g.edges u v = true →
      (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I))
    (hexch : ∀ u v, u ∈ I → v ∉ I →
      (g.edges u v = true ↔ M.Indep (insert v (↑(I.erase u) : Set (Fin n)))))
    (p : List (Fin n)) (hw : SourceWalk g p) (hp : p.Nodup)
    (hmin : ∀ v tail, p = v :: tail → ∀ q, SourceWalk g (v :: q) →
      p.length ≤ (v :: q).length) :
    M.Indep (↑(I ∆ p.toFinset) : Set (Fin n)) ∧
      ∀ v tail, p = v :: tail → v ∈ I →
        M.Indep (insert v (↑(I ∆ p.toFinset) : Set (Fin n))) := by
  classical
  revert hp hmin
  induction hw with
  | source v hs =>
    intro hp hmin
    have hv := (hsrc v).mp hs
    have heq : I ∆ [v].toFinset = insert v I := by
      rw [symmDiff_cons I v [] (by simp), if_neg hv.1]
      congr 1
      ext w
      simp [Finset.mem_symmDiff]
    constructor
    · simpa only [heq, Finset.coe_insert] using hv.2
    · intro w tail he hw
      obtain ⟨hvw, htail⟩ := List.cons.inj he
      subst w
      exact (hv.1 hw).elim
  | step u v tail hw he ih =>
    intro hp hmin
    obtain ⟨hv, hp'⟩ := List.nodup_cons.mp hp
    have hmin' : ∀ w rest, u :: tail = w :: rest → ∀ q,
        SourceWalk g (w :: q) → (u :: tail).length ≤ (w :: q).length := by
      intro w rest heq q hq
      obtain ⟨huw, htail⟩ := List.cons.inj heq
      subst w
      have h := hmin v (u :: tail) rfl (u :: q) (.step u v q hq he)
      simp only [List.length_cons] at h ⊢
      omega
    obtain ⟨hJ, hJundo⟩ := ih hp' hmin'
    rw [symmDiff_cons I v (u :: tail) hv]
    rcases halt u v he with ⟨hu, hvI⟩ | ⟨hu, hvI⟩
    · rw [if_neg hvI]
      have hJbefore := hJundo u tail rfl hu
      have hnotSource : ¬ M.Indep (insert v (I : Set (Fin n))) := by
        intro hvIndep
        have hshort := hmin v (u :: tail) rfl []
          (.source v ((hsrc v).mpr ⟨hvI, hvIndep⟩))
        simp only [List.length_cons, List.length_nil] at hshort
        omega
      have hvE : v ∈ M.E := by rw [hE]; trivial
      have hvcl : v ∈ M.closure (I : Set (Fin n)) := by
        by_contra hnotcl
        exact hnotSource ((hI.notMem_closure_iff_of_notMem hvI hvE).mp hnotcl)
      have hC := hI.fundCircuit_isCircuit hvcl hvI
      have huC : u ∈ M.fundCircuit v (I : Set (Fin n)) := by
        apply (hI.mem_fundCircuit_iff hvcl hvI).mpr
        have hind := (hexch u v hu hvI).mp he
        have heq : insert v (↑(I.erase u) : Set (Fin n)) =
            insert v (I : Set (Fin n)) \ {u} := by
          ext w
          simp only [Finset.coe_erase, Set.mem_insert_iff, Set.mem_sdiff,
            Set.mem_singleton_iff]
          have huv : u ≠ v := by intro heq; subst v; exact hvI hu
          aesop
        rwa [← heq]
      have hCsubset : M.fundCircuit v (I : Set (Fin n)) ⊆
          insert v (insert u (↑(I ∆ (u :: tail).toFinset) : Set (Fin n))) := by
        intro w hwC
        rcases M.fundCircuit_subset_insert v (I : Set (Fin n)) hwC with rfl | hwI
        · exact Or.inl rfl
        · by_cases hwu : w = u
          · subst w
            exact Or.inr (Or.inl rfl)
          · have hwtail : w ∉ tail := by
              intro hwtail
              cases hw with
              | source u hs => simp at hwtail
              | step z u rest hwalk hedge =>
                obtain ⟨q, hq, hlen⟩ := walk_suffix_length hwalk w hwtail
                have hwv : w ≠ v := by intro heq; subst w; exact hvI hwI
                have hwind : M.Indep (insert v (↑(I.erase w) : Set (Fin n))) := by
                  have hind := (hI.mem_fundCircuit_iff hvcl hvI).mp hwC
                  have heq : insert v (↑(I.erase w) : Set (Fin n)) =
                      insert v (I : Set (Fin n)) \ {w} := by
                    ext a
                    simp only [Finset.coe_erase, Set.mem_insert_iff,
                      Set.mem_sdiff, Set.mem_singleton_iff]
                    aesop
                  rwa [heq]
                have hshortcut := (hexch w v hwI hvI).mpr hwind
                have hshort := hmin v (u :: z :: rest) rfl (w :: q)
                  (.step w v q hq hshortcut)
                simp only [List.length_cons] at hshort hlen
                omega
            exact Or.inr (Or.inr (by
              simp only [Finset.mem_coe, Finset.mem_symmDiff, List.mem_toFinset,
                List.mem_cons]
              exact Or.inl ⟨hwI, by simp [hwu, hwtail]⟩))
      have hCeq := hC.eq_fundCircuit_of_subset hJbefore hCsubset
      have hvJ : v ∉ insert u (↑(I ∆ (u :: tail).toFinset) : Set (Fin n)) := by
        have hvu : v ≠ u := by intro heq; subst v; exact hvI hu
        simp only [Set.mem_insert_iff, not_or, Finset.mem_coe,
          Finset.mem_symmDiff, List.mem_toFinset]
        exact ⟨hvu, by simp [hvI, hv]⟩
      have hvclJ : v ∈ M.closure
          (insert u (↑(I ∆ (u :: tail).toFinset) : Set (Fin n))) := by
        have hmem := hC.mem_closure_sdiff_singleton_of_mem
          (M.mem_fundCircuit v (I : Set (Fin n)))
        apply M.closure_subset_closure _ hmem
        intro w hw
        rcases hCsubset hw.1 with heq | hw'
        · exact (hw.2 (by simpa using heq)).elim
        · exact hw'
      have hind := (hJbefore.mem_fundCircuit_iff hvclJ hvJ).mp
        (hCeq ▸ huC)
      have heq : insert v (insert u (↑(I ∆ (u :: tail).toFinset) : Set (Fin n))) \ {u} =
          insert v (↑(I ∆ (u :: tail).toFinset) : Set (Fin n)) := by
        have huJ : u ∉ I ∆ (u :: tail).toFinset := by
          simp [Finset.mem_symmDiff, hu]
        have huv : u ≠ v := by intro heq; subst v; exact hvI hu
        ext w
        constructor
        · rintro ⟨hw, hwu⟩
          rcases hw with hw | hw | hw
          · exact Or.inl hw
          · exact (hwu hw).elim
          · exact Or.inr hw
        · rintro (rfl | hw)
          · exact ⟨Or.inl rfl, Ne.symm huv⟩
          · refine ⟨Or.inr (Or.inr hw), ?_⟩
            intro hwu
            subst w
            exact huJ hw
      constructor
      · simpa only [heq, Finset.coe_insert] using hind
      · intro w rest heq hwI
        obtain ⟨hvw, _⟩ := List.cons.inj heq
        subst w
        exact (hvI hwI).elim
    · rw [if_pos hvI]
      constructor
      · exact hJ.subset (by intro w hw; exact (Finset.mem_erase.mp hw).2)
      · intro w rest heq hwI
        obtain ⟨hvw, _⟩ := List.cons.inj heq
        subst w
        have hvJ : v ∈ I ∆ (u :: tail).toFinset := by
          exact Finset.mem_symmDiff.mpr (Or.inl ⟨hvI, by simpa using hv⟩)
        simpa only [← Finset.coe_insert, Finset.insert_erase hvJ] using hJ
