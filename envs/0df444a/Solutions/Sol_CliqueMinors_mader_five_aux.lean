-- Prove2me | solution 1 for CliqueMinors.mader_five_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:05.437748+00:00
-- url     : https://prove2.me/submissions/ac012379-7d8d-4520-90b1-46e87ca32b44

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Theorems.Thm_CliqueMinors_sum_degree_support
public import Theorems.Thm_CliqueMinors_two_mul_card_edgeFinset_le
public import Theorems.Thm_CliqueMinors_card_edgeFinset_deleteEdge
public import Theorems.Thm_CliqueMinors_card_edge_contract
public import Theorems.Thm_CliqueMinors_card_edges_deleteIncidenceSet
public import Theorems.Thm_CliqueMinors_cone_edges
public import Theorems.Thm_CliqueMinors_contractG_adj
public import Theorems.Thm_CliqueMinors_contract_support
public import Theorems.Thm_CliqueMinors_deleteIncidenceSet_supp
public import Theorems.Thm_CliqueMinors_edges_aux
public import Theorems.Thm_CliqueMinors_isMinor_lift_cone
public import Theorems.Thm_CliqueMinors_isMinor_lift_contract
public import Theorems.Thm_CliqueMinors_isMinor_mono
public import Theorems.Thm_P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
    (∀ a b, G.Adj a b → a ∈ S) → 3 ≤ n → 3 * n ≤ G.edgeFinset.card + 5 →
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  suffices ∀ m (G : SimpleGraph V) (S : Finset V), G.edgeFinset.card = m → S.card = n →
      (∀ a b, G.Adj a b → a ∈ S) → 3 ≤ n → 3 * n ≤ G.edgeFinset.card + 5 →
      IsMinor (⊤ : SimpleGraph (Fin 5)) G from fun G S => this _ G S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G S hm hn hsupp h3 hE
  -- At least five vertices: on three or four vertices there are too few edges.
  have hmax := two_mul_card_edgeFinset_le hsupp
  rw [hn] at hmax
  have h5 : 5 ≤ n := by
    by_contra hlt
    interval_cases n <;> omega
  -- A vertex of degree at most three is deleted.
  by_cases hlow : ∃ x ∈ S, G.degree x ≤ 3
  · obtain ⟨x, hxS, hx⟩ := hlow
    obtain ⟨G', hG'⟩ : ∃ G', G' = G.deleteIncidenceSet x := ⟨_, rfl⟩
    have hE' := card_edges_deleteIncidenceSet G G' x hG'
    have hsupp' : ∀ a b, G'.Adj a b → a ∈ S.erase x := by
      subst hG'; exact deleteIncidenceSet_supp hsupp
    refine isMinor_mono (G' := G') (hG' ▸ deleteIncidenceSet_le' G x) ?_
    refine ihn (n - 1) (by omega) G' (S.erase x) (by rw [Finset.card_erase_of_mem hxS, hn])
      hsupp' (by omega) (by omega)
  push_neg at hlow
  -- An edge whose contraction keeps the density is contracted.
  by_cases hc : ∃ x y, G.Adj x y ∧ 3 * (n - 1) ≤ (contractG G x y).edgeFinset.card + 5
  · obtain ⟨x, y, hxy, hc⟩ := hc
    refine isMinor_lift_contract (G' := contractG G x y) hxy
      (fun u v h => (contractG_adj.1 h).2) (by norm_num) ?_
    have hyS : y ∈ S := hsupp _ _ hxy.symm
    exact ihn (n - 1) (by omega) (contractG G x y) (S.erase y)
      (by rw [Finset.card_erase_of_mem hyS, hn]) (contract_support hxy hsupp) (by omega) hc
  simp only [not_exists, not_and, not_le] at hc
  -- A surplus edge is deleted.
  by_cases hsur : 3 * n < G.edgeFinset.card + 5
  · have hE0 : 0 < G.edgeFinset.card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 hE0
    have hdel := card_edgeFinset_deleteEdge he
    have key : ∀ H : SimpleGraph V, H = G.deleteEdges {e} →
        H.edgeFinset.card + 1 = G.edgeFinset.card := by
      rintro H rfl; convert hdel
    have h' := key _ rfl
    refine isMinor_mono (G' := G.deleteEdges {e}) (deleteEdges_le _) ?_
    refine ihm _ ?_ (G.deleteEdges {e}) S rfl hn
      (fun a b h => hsupp a b (deleteEdges_le _ h)) h3 ?_
    all_goals omega
  -- Now `|E| = 3n - 5`, every vertex has degree at least `4` and every edge lies in at least
  -- three triangles; a vertex of degree at most `5` finishes.
  have hsum := sum_degree_support hsupp
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, G.degree x ≤ 5 := by
    by_contra hno
    push_neg at hno
    have : ∑ v ∈ S, 6 ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum fun v hv => hno v hv
    rw [Finset.sum_const, smul_eq_mul, hn] at this
    omega
  have hx4 := hlow x hxS
  have hcom : ∀ v, G.Adj x v → 3 ≤ (G.neighborFinset x ∩ G.neighborFinset v).card := by
    intro v hv
    have h1 := card_edge_contract hv
    have h2 := hc x v hv
    omega
  have hcone := cone_edges hcom
  rw [card_neighborFinset_eq_degree] at hcone
  refine isMinor_lift_cone (G' := coneG G x) (fun u v h => h) (r := 4) (by norm_num) ?_
  by_contra hK4
  have := edges_aux (G.degree x) (coneG G x) (G.neighborFinset x) (card_neighborFinset_eq_degree _ _)
    (by omega) (fun a b h => by simpa using h.2.1) hK4
  omega
end CliqueMinors
