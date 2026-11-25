-- Prove2me | solution 1 for ErdosPosa.packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:44.168552+00:00
-- url     : https://prove2.me/submissions/bd8f0020-05b5-4601-af83-adba97e2510e

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_ncard_eq_sum_ite
public import Theorems.Thm_ErdosPosa_deg_mono
public import Theorems.Thm_ErdosPosa_psi_deleteEdge
public import Theorems.Thm_ErdosPosa_psi_deleteEdge_of_deg_one
public import Theorems.Thm_ErdosPosa_dsum_deleteEdge
public import Theorems.Thm_ErdosPosa_psi_restr_compl
public import Theorems.Thm_ErdosPosa_cyc_of_cyc_restr_compl
public import Theorems.Thm_ErdosPosa_pairwise_disjoint_cons
public import Theorems.Thm_ErdosPosa_exists_edge_of_psi_pos
public import Theorems.Thm_ErdosPosa_cyc_mono
public import Theorems.Thm_ErdosPosa_exists_minCyc
public import Theorems.Thm_ErdosPosa_restr_adj
public import Theorems.Thm_ErdosPosa_short_cycle
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Fintype V] (g : ℕ → ℕ)
    (hg : ∀ k, (g k : ℤ) + 2 * (2 * Nat.log 2 (g (k + 1) + 1) + 3) ≤ g (k + 1)) :
    ∀ (k : ℕ) (H : SimpleGraph V), (∀ v, deg H v ≤ 3) → (g k : ℤ) ≤ psi H →
      ∃ T : Fin k → Set V, Pairwise (fun i j => Disjoint (T i) (T j)) ∧ ∀ i, Cyc H (T i) := by
  intro k
  induction k with
  | zero => intro _ _ _; exact ⟨Fin.elim0, fun i _ _ => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
  intro H hdeg hpsi
  classical
  have hex : ∃ n, ∃ H₀ ≤ H, (g (k + 1) : ℤ) ≤ psi H₀ ∧ dsum H₀ = n := ⟨_, H, le_rfl, hpsi, rfl⟩
  obtain ⟨H₀, hle, hpsi0, hn⟩ := Nat.find_spec hex
  have hmin : ∀ H₁ ≤ H, (g (k + 1) : ℤ) ≤ psi H₁ → ¬ dsum H₁ < dsum H₀ := by
    intro H₁ h1 h2 hlt
    exact Nat.find_min hex (hn ▸ hlt) ⟨H₁, h1, h2, rfl⟩
  have hdeg0 : ∀ v, deg H₀ v ≤ 3 := fun v => (deg_mono hle v).trans (hdeg v)
  have hgpos : (0 : ℤ) < g (k + 1) := by have := hg k; omega
  have hedge : ∃ u w, H₀.Adj u w := exists_edge_of_psi_pos (by omega)
  have hno1 : ∀ v, deg H₀ v ≠ 1 := by
    intro v hv
    obtain ⟨z, hz⟩ : ∃ z, H₀.Adj v z := by
      have : 0 < (H₀.neighborSet v).ncard := by rw [← deg]; omega
      obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.toFinite _)).1 this
      exact ⟨z, hz⟩
    exact hmin _ ((deleteEdges_le _).trans hle)
      (hpsi0.trans (psi_deleteEdge_of_deg_one hz hv)) (dsum_deleteEdge hz)
  have hup : psi H₀ ≤ g (k + 1) + 1 := by
    by_contra hcon
    obtain ⟨y, z, hyz⟩ := hedge
    have := psi_deleteEdge hyz
    exact hmin _ ((deleteEdges_le _).trans hle) (by omega) (dsum_deleteEdge hyz)
  have hdegs : ∀ v, deg H₀ v = 0 ∨ deg H₀ v = 2 ∨ deg H₀ v = 3 := by
    intro v; have := hdeg0 v; have := hno1 v; omega
  have hcount : ({v | deg H₀ v = 3}.ncard : ℤ) = psi H₀ := by
    rw [ncard_eq_sum_ite]
    push_cast
    unfold psi
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rcases hdegs v with h | h | h <;> simp [h, wt]
  have hm' : {v | deg H₀ v = 3}.ncard ≤ g (k + 1) + 1 := by omega
  obtain ⟨S, hS, hScnt⟩ := short_cycle H₀ hdegs _ hm' hedge
  obtain ⟨T, hTS, hT⟩ := exists_minCyc hS
  have hTcnt : {t | t ∈ T ∧ deg H₀ t = 3}.ncard ≤ 2 * Nat.log 2 (g (k + 1) + 1) + 3 :=
    (Set.ncard_le_ncard (s := {t | t ∈ T ∧ deg H₀ t = 3}) (t := {v | v ∈ S ∧ deg H₀ v = 3})
      (fun t ht => ⟨hTS ht.1, ht.2⟩) (Set.toFinite _)).trans hScnt
  have hpsi' := psi_restr_compl hT hdeg0
  have hle' : restr H₀ Tᶜ ≤ H₀ := fun a b h => h.1
  obtain ⟨T', hT'disj, hT'cyc⟩ := ih (restr H₀ Tᶜ)
    (fun v => (deg_mono hle' v).trans (hdeg0 v)) (by have := hg k; omega)
  refine ⟨Fin.cons T (fun i => T' i \ T), ?_, ?_⟩
  · refine pairwise_disjoint_cons _ _ ?_ ?_
    · intro i j hij
      exact (hT'disj hij).mono Set.sdiff_subset Set.sdiff_subset
    · intro i
      exact Set.disjoint_sdiff_right
  · intro i
    induction i using Fin.cases with
    | zero => simpa using cyc_mono hT.1 hle subset_rfl
    | succ i =>
      simp only [Fin.cons_succ]
      exact cyc_mono (cyc_of_cyc_restr_compl (hT'cyc i)) hle subset_rfl
end ErdosPosa
