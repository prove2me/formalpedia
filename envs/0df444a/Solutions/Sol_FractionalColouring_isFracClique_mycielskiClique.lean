-- Prove2me | solution 1 for FractionalColouring.isFracClique_mycielskiClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:51:03.802306+00:00
-- url     : https://prove2.me/submissions/4fc721d5-0024-49aa-8f35-8256970344e6

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_original_mem_lift
public import Theorems.Thm_FractionalColouring_shadow_mem_lift
public import Theorems.Thm_FractionalColouring_none_not_mem_lift
public import Theorems.Thm_FractionalColouring_original_mem_liftApex
public import Theorems.Thm_FractionalColouring_shadow_not_mem_liftApex
public import Theorems.Thm_FractionalColouring_none_mem_liftApex
public import Theorems.Thm_FractionalColouring_original_not_mem_shadows
public import Theorems.Thm_FractionalColouring_shadow_mem_shadows
public import Theorems.Thm_FractionalColouring_none_not_mem_shadows
public import Theorems.Thm_FractionalColouring_sum_mycielskiClique
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_FractionalColouring_isFracColouring_singletons
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_shadow_adj_original
attribute [local simp] FiniteLP.toE_apply
attribute [local simp] Mycielski.apex_adj_shadow
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.shadow_adj_original


attribute [local simp] FractionalColouring.original_mem_lift
attribute [local simp] FractionalColouring.shadow_mem_lift
attribute [local simp] FractionalColouring.none_not_mem_lift
attribute [local simp] FractionalColouring.original_mem_liftApex
attribute [local simp] FractionalColouring.shadow_not_mem_liftApex
attribute [local simp] FractionalColouring.none_mem_liftApex
attribute [local simp] FractionalColouring.original_not_mem_shadows
attribute [local simp] FractionalColouring.shadow_mem_shadows
attribute [local simp] FractionalColouring.none_not_mem_shadows

set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution {g : V → ℝ} (hg : IsFracClique G g) {a : ℝ} (ha : 1 ≤ a)
    (hga : ∀ x, IsFracColouring G x → ∀ (T : Finset V) (c : ℝ), 0 ≤ c →
      (∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c) →
        ∑ v ∈ T, g v ≤ c * a) :
    IsFracClique (graph G) (mycielskiClique g a) := by
  have ha0 : 0 < a := by linarith
  have hc : 0 ≤ 1 - 1 / a := by
    rw [sub_nonneg, div_le_one ha0]; exact ha
  refine ⟨fun u => ?_, fun S hS => ?_⟩
  · rcases u with _ | ⟨v, _ | _⟩
    · exact div_nonneg zero_le_one ha0.le
    · exact mul_nonneg hc (hg.1 v)
    · exact div_nonneg (hg.1 v) ha0.le
  set J := univ.filter (fun v => original v ∈ S) with hJ
  set K := univ.filter (fun v => shadow v ∈ S) with hK
  rw [sum_mycielskiClique, ← hJ, ← hK]
  -- `J` is independent in `G`
  have hJi : G.IsIndepSet (J : Set V) := by
    intro v hv w hw hvw
    simp only [hJ, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    exact hS hv hw (fun h => hvw (by simpa [original] using h))
  -- no edges between `J` and `K`
  have hJK : ∀ j ∈ J, ∀ k ∈ K, ¬ G.Adj j k := by
    intro j hj k hk
    simp only [hJ, hK, mem_filter, mem_univ, true_and] at hj hk
    simpa using hS hj hk (by simp [original, shadow])
  have hgJ : ∑ v ∈ J, g v ≤ 1 := hg.2 J hJi
  have hgJ0 : 0 ≤ ∑ v ∈ J, g v := Finset.sum_nonneg fun v _ => hg.1 v
  by_cases hn : none ∈ S
  · -- the apex excludes every shadow
    have hK0 : K = ∅ := by
      ext k
      simp only [hK, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hk
      exact hS hn hk (by simp [shadow]) (apex_adj_shadow G k)
    rw [if_pos hn, hK0, Finset.sum_empty, zero_div, add_zero]
    have : (1 - 1 / a) * ∑ v ∈ J, g v ≤ 1 - 1 / a := mul_le_of_le_one_right hc hgJ
    linarith
  · rw [if_neg hn, zero_add]
    -- `g(K) ≤ g(J) + (1 − g(J)) a`
    have hsplit := Finset.sum_inter_add_sum_sdiff K J g
    have h1 : ∑ v ∈ K ∩ J, g v ≤ ∑ v ∈ J, g v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun v _ _ => hg.1 v)
    have h2 : ∑ v ∈ K \ J, g v ≤ (1 - ∑ v ∈ J, g v) * a := by
      refine hga _ isFracColouring_singletons (K \ J) _ (by linarith) fun s hs => ?_
      -- `J ∪ ((K \ J) ∩ s)` is independent
      have hdisj : Disjoint J ((K \ J) ∩ s) :=
        Finset.disjoint_left.mpr fun v hvJ hv => (Finset.mem_sdiff.mp
          (Finset.mem_inter.mp hv).1).2 hvJ
      have hind : G.IsIndepSet ((J ∪ (K \ J) ∩ s : Finset V) : Set V) := by
        rw [coe_union, SimpleGraph.IsIndepSet, Set.pairwise_union]
        refine ⟨hJi, fun v hv w hw hvw => hs (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hw).2 hvw,
          fun v hv w hw _ => ?_⟩
        have hwK := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).1).1
        exact ⟨fun h => hJK v hv w hwK h, fun h => hJK v hv w hwK h.symm⟩
      have := hg.2 _ hind
      rw [Finset.sum_union hdisj] at this
      linarith
    have hKle : ∑ v ∈ K, g v ≤ ∑ v ∈ J, g v + (1 - ∑ v ∈ J, g v) * a := by linarith
    have : (∑ v ∈ K, g v) / a ≤ (∑ v ∈ J, g v) / a + (1 - ∑ v ∈ J, g v) := by
      rw [div_le_iff₀ ha0]
      have : ((∑ v ∈ J, g v) / a + (1 - ∑ v ∈ J, g v)) * a =
          ∑ v ∈ J, g v + (1 - ∑ v ∈ J, g v) * a := by field_simp
      linarith
    have h3 : (1 - 1 / a) * ∑ v ∈ J, g v + (∑ v ∈ J, g v) / a = ∑ v ∈ J, g v := by
      field_simp; ring
    linarith
end FractionalColouring
