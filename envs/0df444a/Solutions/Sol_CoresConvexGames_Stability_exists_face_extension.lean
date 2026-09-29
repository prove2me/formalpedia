-- Prove2me | solution 1 for CoresConvexGames.Stability.exists_face_extension
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:28.358565+00:00
-- url     : https://prove2.me/submissions/df660f55-3fb5-4bd2-a08e-3db2a3cb9d67

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

theorem aux_cfe_core_le {n : ℕ} (f : Finset (Fin n) → ℝ) (y : Fin n → ℝ)
    (hy : y ∈ Core Finset.univ f) (i : Fin n) :
    f {i} ≤ y i ∧ y i ≤ f Finset.univ - ∑ k, f {k} + f {i} := by
  obtain ⟨hsum, hle⟩ := hy
  have h1 : ∀ k, f {k} ≤ y k := fun k => by
    have := hle {k} (Finset.subset_univ _)
    simpa using this
  refine ⟨h1 i, ?_⟩
  have h2 : y i - f {i} ≤ ∑ k, (y k - f {k}) :=
    Finset.single_le_sum (f := fun k => y k - f {k}) (fun k _ => sub_nonneg.mpr (h1 k))
      (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib, hsum] at h2
  linarith

theorem aux_cfe_main {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hreg : IsRegularConfiguration f) (S : Finset (Fin n)) (a : Fin n → ℝ)
    (ha : a ∈ CoreFace f S) (j : Fin n) (hj : j ∉ S) :
    ∃ b ∈ CoreFace f S ∩ CoreFace f (insert j S), ∀ i ∈ S, b i = a i := by
  classical
  set F : Set (Fin n → ℝ) := {y | ∑ i, y i = f Finset.univ} ∩
    (⋂ T : Finset (Fin n), {y | f T ≤ ∑ i ∈ T, y i}) ∩ (⋂ i ∈ S, {y | y i = a i}) with hF
  have memF : ∀ y, y ∈ F ↔ y ∈ Core Finset.univ f ∧ ∀ i ∈ S, y i = a i := by
    intro y
    simp only [hF, Core, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Finset.subset_univ, forall_const]
  have hFclosed : IsClosed F := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    · exact isClosed_iInter fun T =>
        isClosed_le continuous_const (continuous_finsetSum _ fun i _ => continuous_apply i)
    · exact isClosed_biInter fun i _ => isClosed_eq (continuous_apply i) continuous_const
  have hFsub : F ⊆ Set.Icc (fun i => f {i}) (fun i => f Finset.univ - ∑ k, f {k} + f {i}) := by
    intro y hy
    have hc := ((memF y).1 hy).1
    exact ⟨fun i => (aux_cfe_core_le f y hc i).1, fun i => (aux_cfe_core_le f y hc i).2⟩
  have hFcpt : IsCompact F := (isCompact_Icc).of_isClosed_subset hFclosed hFsub
  have haF : a ∈ F := (memF a).2 ⟨ha.1, fun i _ => rfl⟩
  obtain ⟨b, hbF, hbmin⟩ := hFcpt.exists_isMinOn ⟨a, haF⟩ (continuous_apply j).continuousOn
  obtain ⟨hbC, hbS⟩ := (memF b).1 hbF
  have hbCS : b ∈ CoreFace f S := by
    refine ⟨hbC, fun hne => ?_⟩
    rw [Finset.sum_congr rfl hbS]
    exact ha.2 hne
  have key : ∀ k, k ∉ insert j S → ∃ U, b ∈ CoreFace f U ∧ j ∈ U ∧ k ∉ U := by
    intro k hk
    have hkj : k ≠ j := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    by_contra hcon
    push Not at hcon
    set Fam := Finset.univ.filter (fun U : Finset (Fin n) => j ∈ U ∧ k ∉ U) with hFam
    have hne : Fam.Nonempty := ⟨{j}, by simp [hFam, hkj]⟩
    set ε := Fam.inf' hne (fun U => ∑ i ∈ U, b i - f U) with hε
    have hstrict : ∀ U, j ∈ U → k ∉ U → f U < ∑ i ∈ U, b i := by
      intro U hjU hkU
      have hle := hbC.2 U (Finset.subset_univ _)
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd hkU (not_not.2 (hcon U ⟨hbC, fun _ => h.symm⟩ hjU))
    have hεpos : 0 < ε := by
      rw [hε, Finset.lt_inf'_iff]
      intro U hU
      simp only [hFam, Finset.mem_filter] at hU
      linarith [hstrict U hU.2.1 hU.2.2]
    have hεle : ∀ U, j ∈ U → k ∉ U → ε ≤ ∑ i ∈ U, b i - f U := by
      intro U hjU hkU
      exact Finset.inf'_le _ (by simp [hFam, hjU, hkU])
    set b' : Fin n → ℝ := fun i => b i + ε * ((Pi.single k (1:ℝ) : Fin n → ℝ) i - (Pi.single j (1:ℝ) : Fin n → ℝ) i)
      with hb'
    have hsum' : ∀ T : Finset (Fin n), ∑ i ∈ T, b' i =
        ∑ i ∈ T, b i + ε * ((if k ∈ T then 1 else 0) - (if j ∈ T then 1 else 0)) := by
      intro T
      simp only [hb', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_pi_single']
    have hb'F : b' ∈ F := by
      rw [memF]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hsum']; simp [hbC.1]
      · intro T _
        rw [hsum']
        have hT := hbC.2 T (Finset.subset_univ _)
        by_cases hjT : j ∈ T <;> by_cases hkT : k ∈ T
        · simp [hjT, hkT]; exact hT
        · have := hεle T hjT hkT; simp [hjT, hkT]; linarith
        · simp [hjT, hkT]; linarith
        · simp [hjT, hkT]; exact hT
      · intro i hi
        have hik : i ≠ k := fun h => hkS (h ▸ hi)
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp [hb', Pi.single_apply, hik, hij, hbS i hi]
    have hmin := hbmin hb'F
    simp only [Set.mem_ofPred_eq] at hmin
    have hb'j : b' j = b j - ε := by simp [hb', Pi.single_apply, hkj.symm]; ring
    linarith
  have inter : ∀ R : Finset (Fin n), (∀ k ∈ R, k ∉ insert j S) →
      ∃ U, b ∈ CoreFace f U ∧ j ∈ U ∧ Disjoint U R := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Finset.univ, ⟨hbC, fun _ => hbC.1⟩, Finset.mem_univ _,
        Finset.disjoint_empty_right _⟩
    | insert k R hkR ih =>
      intro hR
      obtain ⟨U, hU, hjU, hdis⟩ := ih (fun x hx => hR x (Finset.mem_insert_of_mem hx))
      obtain ⟨V, hV, hjV, hkV⟩ := key k (hR k (Finset.mem_insert_self _ _))
      refine ⟨U ∩ V, (hreg.2 U V ⟨hU, hV⟩).2, Finset.mem_inter.2 ⟨hjU, hjV⟩, ?_⟩
      rw [Finset.disjoint_insert_right]
      exact ⟨fun h => hkV (Finset.mem_inter.1 h).2,
        Finset.disjoint_of_subset_left Finset.inter_subset_left hdis⟩
  obtain ⟨U, hU, hjU, hdis⟩ :=
    inter (Finset.univ \ insert j S) (fun k hk => (Finset.mem_sdiff.1 hk).2)
  have hUsub : U ⊆ insert j S := by
    intro x hx
    by_contra hx'
    exact Finset.disjoint_left.1 hdis hx (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx'⟩)
  have hUS : U ∪ S = insert j S := by
    apply Finset.Subset.antisymm (Finset.union_subset hUsub (Finset.subset_insert _ _))
    intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · exact Finset.mem_union_left _ (h ▸ hjU)
    · exact Finset.mem_union_right _ h
  have hbJ : b ∈ CoreFace f (insert j S) := by
    have := (hreg.2 U S ⟨hU, hbCS⟩).1
    rwa [hUS] at this
  exact ⟨b, ⟨hbCS, hbJ⟩, hbS⟩

end CoresConvexGames.Stability

open CoresConvexGames.Stability

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S : Finset (Fin n)) (hS : S ⊂ Finset.univ)
    (hcard : S.card + 2 ≤ n) (a : Fin n → ℝ) (ha : a ∈ CoreFace f S)
    (j : Fin n) (hj : j ∉ S) :
    ∃ b ∈ CoreFace f S ∩ CoreFace f (insert j S), ∀ i ∈ S, b i = a i :=
  aux_cfe_main f hreg S a ha j hj
