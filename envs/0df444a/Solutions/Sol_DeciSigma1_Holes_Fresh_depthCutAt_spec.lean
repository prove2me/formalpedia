-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCutAt_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:50.477306+00:00
-- url     : https://prove2.me/submissions/8a8cc806-45b0-4921-b3bd-ead7d06b9c36

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_split
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_self
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {s e : ℕ} (hse : s < e) (he : e ∈ A) (hs : s = 0 ∨ s ∈ A) :
    (∀ d < anchorCount A s e, depthCutAt A e d ∈ A ∧ s < depthCutAt A e d ∧ depthCutAt A e d ≤ e ∧
      anchorCount A (depthCutAt A e d) e = d) ∧ depthCutAt A e (anchorCount A s e) = s := by
  have hn : 1 ≤ anchorCount A s e := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hse, le_rfl⟩⟩
  have main : ∀ d < anchorCount A s e, depthCutAt A e d ∈ A ∧ s < depthCutAt A e d ∧
      depthCutAt A e d ≤ e ∧
      anchorCount A (depthCutAt A e d) e = d := by
    intro d
    induction d with
    | zero => intro _; exact ⟨he, hse, le_rfl, anchorCount_self e⟩
    | succ d ih =>
      intro hd
      obtain ⟨hpA, hsp, hpe, hcnt⟩ := ih (by omega)
      set p := depthCutAt A e d with hp
      have hsplit := anchorCount_split (A := A) hsp.le hpe
      have hsp2 : 2 ≤ anchorCount A s p := by omega
      -- an element of `A` strictly between `s` and `p`
      have hex : ∃ q ∈ A, s < q ∧ q < p := by
        by_contra hno
        simp only [not_exists, not_and, not_lt] at hno
        have : anchorCount A s p ≤ 1 := by
          unfold anchorCount
          rw [card_le_one]
          intro a ha b hb
          simp only [mem_filter] at ha hb
          have ha' : a = p := by
            by_contra hne; exact absurd (hno a ha.1 ha.2.1) (by omega)
          have hb' : b = p := by
            by_contra hne; exact absurd (hno b hb.1 hb.2.1) (by omega)
          rw [ha', hb']
        omega
      obtain ⟨q, hqA, hsq, hqp⟩ := hex
      obtain ⟨hprA, hprp⟩ := previousAnchor_spec ⟨q, hqA, hqp⟩
      have hqpr := le_previousAnchor hqA hqp
      change previousAnchor A p ∈ A ∧ s < previousAnchor A p ∧ previousAnchor A p ≤ e ∧
          anchorCount A (previousAnchor A p) e = d + 1
      refine ⟨hprA, by omega, by omega, ?_⟩
      rw [anchorCount_split (A := A) hprp.le hpe, hcnt]
      have : anchorCount A (previousAnchor A p) p = 1 := by
        unfold anchorCount
        rw [card_eq_one]
        refine ⟨p, ?_⟩
        ext r
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hr, h1, h2⟩
          by_contra hne
          have := le_previousAnchor hr (show r < p by omega)
          omega
        · rintro rfl; exact ⟨hpA, hprp, le_rfl⟩
      omega
  refine ⟨main, ?_⟩
  obtain ⟨n, hn'⟩ : ∃ n, anchorCount A s e = n + 1 := ⟨anchorCount A s e - 1, by omega⟩
  rw [hn']
  obtain ⟨hpA, hsp, hpe, hcnt⟩ := main n (by omega)
  change previousAnchor A (depthCutAt A e n) = s
  have hsplit := anchorCount_split (A := A) hsp.le hpe
  have h1 : anchorCount A s (depthCutAt A e n) = 1 := by omega
  have hno : ∀ q ∈ A, q < depthCutAt A e n → q ≤ s := by
    intro q hq hqp
    by_contra hqs
    have : 2 ≤ anchorCount A s (depthCutAt A e n) := by
      unfold anchorCount
      have hsub : ({q, depthCutAt A e n} : Finset ℕ) ⊆
          A.filter (fun p => s < p ∧ p ≤ depthCutAt A e n) := by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact mem_filter.mpr ⟨hq, by omega, hqp.le⟩
        · exact mem_filter.mpr ⟨hpA, hsp, le_rfl⟩
      have := card_le_card hsub
      rw [card_pair (by omega)] at this
      exact this
    omega
  apply le_antisymm (previousAnchor_le hno)
  rcases hs with hs0 | hsA
  · omega
  · exact le_previousAnchor hsA hsp
end DeciSigma1.Holes.Fresh
