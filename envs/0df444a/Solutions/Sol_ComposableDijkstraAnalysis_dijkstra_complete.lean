-- Prove2me | solution 1 for ComposableDijkstraAnalysis.dijkstra_complete
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:00.484023+00:00
-- url     : https://prove2.me/submissions/97a2d43d-4dc8-47dd-b135-fcc264515541

import Definitions.Def_Algo_dijkstra_dijkstra_Analysis
import Theorems.Thm_ComposableDijkstraAnalysis_extraction_progress


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable shortest-path mathematics for Dijkstra implementations.

This module imports neither a compiled algorithm nor the Algo2Lean runtime.
Distance sequences are ordinary functions `Int → Int`. A queue backend only
needs to supply minimum selection, the relaxation scan, and exhaustion; the
path, frontier, and shortest-distance proofs are shared across backends.
-/

namespace Algo2Lean.Dijkstra

















/-- The minimum unsettled tentative distance bounds every route ending in the
    unsettled region. Settled optimality establishes the bound at the first
    frontier crossing; nonnegative edge weights preserve it along the remaining route. -/
theorem unsettled_path_lower_bound (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (settledCorrect : SettledOptimal edge source distance settled)
    (frontier : FrontierBound edge distance settled)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
      distance selected ≤ distance vertex)
    (vertex cost : Int) (path : Path edge source vertex cost) (unsettled : ¬ settled vertex) :
    distance selected ≤ cost := by
  induction path with
  | empty =>
    have sourceZero := sourceInitialized unsettled
    have bound := minimum source unsettled (by omega)
    omega
  | @extend previous vertex prefixCost weight route connection inductionHypothesis =>
    by_cases previousSettled : settled previous
    · have previousBound := settledCorrect previous previousSettled prefixCost route
      obtain ⟨finite, relaxed⟩ := frontier previous vertex weight previousSettled unsettled connection
      have selectedBound := minimum vertex unsettled finite
      omega
    · have prefixBound := inductionHypothesis previousSettled
      have weightNonnegative := nonnegative previous vertex weight connection
      omega

/-- Greedy safety: choosing a minimum finite unsettled distance never settles
    a value larger than the weight of a route to the selected vertex. -/
theorem greedy_safe (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (settledCorrect : SettledOptimal edge source distance settled)
    (frontier : FrontierBound edge distance settled)
    (selectedUnsettled : ¬ settled selected)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
      distance selected ≤ distance vertex) :
    ∀ cost, Path edge source selected cost → distance selected ≤ cost := by
  intro cost path
  exact unsettled_path_lower_bound edge source selected distance settled nonnegative
    sourceInitialized settledCorrect frontier minimum selected cost path selectedUnsettled



/-- Settling the selected vertex preserves the settled-distance invariant.
    Restoring `FrontierBound` afterwards requires relaxing its outgoing edges. -/
theorem settle_preserves_optimality (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (settledCorrect : SettledOptimal edge source distance settled)
    (selectedCorrect : ∀ cost, Path edge source selected cost → distance selected ≤ cost) :
    SettledOptimal edge source distance (fun vertex => settled vertex ∨ vertex = selected) := by
  intro vertex newlySettled cost path
  rcases newlySettled with alreadySettled | rfl
  · exact settledCorrect vertex alreadySettled cost path
  · exact selectedCorrect cost path

/-- If no finite unsettled distance remains, every reachable vertex is settled.
    Only source initialization and the relaxed frontier are needed here. -/
theorem reachable_settled_of_exhausted (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (frontier : FrontierBound edge distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0)
    (vertex cost : Int) (path : Path edge source vertex cost) : settled vertex := by
  induction path with
  | empty =>
    by_cases sourceSettled : settled source
    · exact sourceSettled
    · have sourceZero := sourceInitialized sourceSettled
      have sourceAbsent := exhausted source sourceSettled
      omega
  | @extend previous vertex prefixCost weight route connection previousSettled =>
    by_cases vertexSettled : settled vertex
    · exact vertexSettled
    · have finite := (frontier previous vertex weight previousSettled vertexSettled connection).1
      have absent := exhausted vertex vertexSettled
      omega

/-- Unsettled vertices are unreachable when the finite priority queue is empty. -/
theorem exhausted_unreachable (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (frontier : FrontierBound edge distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0)
    (vertex : Int) (unsettled : ¬ settled vertex) :
    ∀ cost, ¬ Path edge source vertex cost := by
  intro cost path
  exact unsettled (reachable_settled_of_exhausted edge source distance settled
    sourceInitialized frontier exhausted vertex cost path)









theorem vertexRange_nodup (size : Int) : (vertexRange size).Nodup := by
  exact List.Pairwise.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same)) List.nodup_range





/-- Each settlement consumes exactly one remaining vertex. -/
theorem remaining_length (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    (remaining.erase selected).length + 1 = remaining.length := by
  have positive := List.length_pos_of_mem member
  rw [List.length_erase_of_mem member]
  omega







/-- Removing one list entry removes exactly its contribution to any natural
    weighted sum. This does not need a no-duplicates assumption. -/
theorem weighted_sum_erase (weight : Int → Nat) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    ((remaining.erase selected).map weight).sum + weight selected = (remaining.map weight).sum := by
  induction remaining with
  | nil => simp at member
  | cons vertex rest ih =>
    by_cases same : selected = vertex
    · subst selected
      simp [Nat.add_comm]
    · have inRest : selected ∈ rest := by simpa [same] using member
      have shorter := ih inRest
      simpa [List.erase_cons, same, Ne.symm same, Nat.add_assoc] using
        congrArg (fun total => weight vertex + total) shorter

theorem edgeBudget_erase (adjacency : Adjacency) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    edgeBudget adjacency (remaining.erase selected) + (adjacency selected).length =
      edgeBudget adjacency remaining :=
  weighted_sum_erase (fun vertex => (adjacency vertex).length) remaining selected member











/-! Pure invariants for every iteration of Dijkstra, independent of the queue
implementation, storage layout, and compiler-generated transition system. -/









theorem relax_distance_other (distance : Int → Int) (target candidate vertex : Int)
    (different : vertex ≠ target) : relaxDistance distance target candidate vertex = distance vertex := by
  by_cases better : distance target < 0 ∨ candidate < distance target
  <;> simp [relaxDistance, updateDistance, better, different]

/-- Relaxation creates a finite bound for the target, even if it was unknown. -/
theorem relax_distance_target (distance : Int → Int) (target candidate : Int) (nonnegative : 0 ≤ candidate) :
    0 ≤ relaxDistance distance target candidate target ∧
      relaxDistance distance target candidate target ≤ candidate := by
  by_cases better : distance target < 0 ∨ candidate < distance target
  · simp [relaxDistance, updateDistance, better, nonnegative]
  · simp only [relaxDistance, if_neg better]
    omega

/-- A finite distance never increases, and every earlier upper bound survives. -/
theorem relax_distance_preserves_bound (distance : Int → Int) (target candidate vertex bound : Int)
    (nonnegative : 0 ≤ candidate) (finite : 0 ≤ distance vertex) (bounded : distance vertex ≤ bound) :
    0 ≤ relaxDistance distance target candidate vertex ∧
      relaxDistance distance target candidate vertex ≤ bound := by
  by_cases same : vertex = target
  · subst vertex
    by_cases better : distance target < 0 ∨ candidate < distance target
    · simp only [relaxDistance, if_pos better, update_distance_same]
      exact ⟨nonnegative, by omega⟩
    · simp [relaxDistance, better, finite, bounded]
  · rw [relax_distance_other distance target candidate vertex same]
    exact ⟨finite, bounded⟩

theorem relax_distance_preserves_zero (distance : Int → Int) (target candidate vertex : Int)
    (nonnegative : 0 ≤ candidate) (zero : distance vertex = 0) :
    relaxDistance distance target candidate vertex = 0 := by
  have bounded := relax_distance_preserves_bound distance target candidate vertex 0 nonnegative
    (by omega) (by omega)
  omega









/-- Greedy minimum selection permits settling exactly one vertex. The edge
    scan starts with an empty processed list and retains all older bounds. -/
theorem start_relaxation (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge) (invariant : SearchInvariant edge source distance settled)
    (unsettled : ¬ settled selected) (finite : 0 ≤ distance selected)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex → distance selected ≤ distance vertex) :
    RelaxationInvariant edge source distance (settleVertex settled selected) selected [] := by
  refine ⟨⟨?_, invariant.witnesses, ?_, ?_, invariant.unknown⟩, Or.inr rfl, ?_, ?_⟩
  · intro sourceUnsettled
    exact invariant.sourceZero (fun present => sourceUnsettled (Or.inl present))
  · exact settle_preserves_optimality edge source selected distance settled invariant.settledOptimal
      (greedy_safe edge source selected distance settled nonnegative invariant.sourceZero
        invariant.settledOptimal invariant.frontier unsettled minimum)
  · intro vertex present
    rcases present with old | rfl
    · exact invariant.settledFinite vertex old
    · exact finite
  · intro u v weight present different notSettled connection
    rcases present with old | same
    · exact invariant.frontier u v weight old (fun yes => notSettled (Or.inl yes)) connection
    · exact False.elim (different same)
  · intro v weight member
    simp at member

theorem DistanceInvariant.relax (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (invariant : DistanceInvariant edge source distance settled)
    (connection : edge selected target weight) (selectedFinite : 0 ≤ distance selected)
    (weightNonnegative : 0 ≤ weight) (targetUnsettled : ¬ settled target) :
    DistanceInvariant edge source (relaxDistance distance target (distance selected + weight)) settled := by
  have candidateNonnegative : 0 ≤ distance selected + weight := by omega
  have candidateRoute : Path edge source target (distance selected + weight) :=
    Path.extend (invariant.witnesses selected selectedFinite) connection
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sourceUnsettled
    exact relax_distance_preserves_zero distance target _ source candidateNonnegative
      (invariant.sourceZero sourceUnsettled)
  · intro vertex finite
    by_cases better : distance target < 0 ∨ distance selected + weight < distance target
    · by_cases same : vertex = target
      · subst vertex
        simpa [relaxDistance, better] using candidateRoute
      · rw [relax_distance_other distance target _ vertex same] at finite ⊢
        exact invariant.witnesses vertex finite
    · simpa [relaxDistance, better] using invariant.witnesses vertex (by simpa [relaxDistance, better] using finite)
  · intro vertex present cost path
    have different : vertex ≠ target := by intro same; exact targetUnsettled (same ▸ present)
    rw [relax_distance_other distance target _ vertex different]
    exact invariant.settledOptimal vertex present cost path
  · intro vertex present
    have different : vertex ≠ target := by intro same; exact targetUnsettled (same ▸ present)
    rw [relax_distance_other distance target _ vertex different]
    exact invariant.settledFinite vertex present
  · intro vertex negative
    by_cases same : vertex = target
    · subst vertex
      have finite := (relax_distance_target distance target _ candidateNonnegative).1
      omega
    · rw [relax_distance_other distance target _ vertex same] at negative ⊢
      exact invariant.unknown vertex negative

/-- Processing an unsettled target preserves every earlier relaxation and
    establishes the new edge's bound. The `relaxDistance` branch covers both
    actual improvements and unsuccessful comparisons. -/
theorem relax_unsettled_edge (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (connection : edge selected target weight) (weightNonnegative : 0 ≤ weight)
    (targetUnsettled : ¬ settled target) :
    RelaxationInvariant edge source (relaxDistance distance target (distance selected + weight))
      settled selected ((target, weight) :: processed) := by
  have selectedFinite := invariant.settledFinite selected invariant.selectedSettled
  have candidateNonnegative : 0 ≤ distance selected + weight := by omega
  have selectedDifferent : selected ≠ target := by
    intro same; exact targetUnsettled (same ▸ invariant.selectedSettled)
  refine ⟨DistanceInvariant.relax edge source selected target weight distance settled
    invariant.toDistanceInvariant connection selectedFinite weightNonnegative targetUnsettled,
    invariant.selectedSettled, ?_, ?_⟩
  · intro u v edgeWeight uSettled different vUnsettled edgeExists
    have uDifferent : u ≠ target := by intro same; exact targetUnsettled (same ▸ uSettled)
    rw [relax_distance_other distance target _ u uDifferent]
    obtain ⟨finite, bound⟩ := invariant.oldFrontier u v edgeWeight uSettled different vUnsettled edgeExists
    exact relax_distance_preserves_bound distance target _ v _ candidateNonnegative finite bound
  · intro v edgeWeight member vUnsettled
    rw [relax_distance_other distance target _ selected selectedDifferent]
    simp only [List.mem_cons] at member
    rcases member with same | earlier
    · cases same
      exact relax_distance_target distance target _ candidateNonnegative
    · obtain ⟨finite, bound⟩ := invariant.processedFrontier v edgeWeight earlier vUnsettled
      exact relax_distance_preserves_bound distance target _ v _ candidateNonnegative finite bound

theorem skip_settled_edge (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (targetSettled : settled target) :
    RelaxationInvariant edge source distance settled selected ((target, weight) :: processed) := by
  refine ⟨invariant.toDistanceInvariant, invariant.selectedSettled, invariant.oldFrontier, ?_⟩
  intro v edgeWeight member vUnsettled
  simp only [List.mem_cons] at member
  rcases member with same | earlier
  · cases same
    exact False.elim (vUnsettled targetSettled)
  · exact invariant.processedFrontier v edgeWeight earlier vUnsettled

/-- Once the whole outgoing list is processed, the ordinary outer-loop
    invariant has been restored for every settled vertex. -/
theorem finish_relaxation (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (complete : ∀ target weight, edge selected target weight → (target, weight) ∈ processed) :
    SearchInvariant edge source distance settled := by
  refine ⟨invariant.toDistanceInvariant, ?_⟩
  intro u v weight present notSettled connection
  by_cases selectedVertex : u = selected
  · subst u
    exact invariant.processedFrontier v weight (complete v weight connection) notSettled
  · exact invariant.oldFrontier u v weight present selectedVertex notSettled connection



theorem initial_search_invariant (edge : Edges) (source : Int) :
    SearchInvariant edge source (initialDistances source) (fun _ => False) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro _; simp [initialDistances]
  · intro vertex finite
    by_cases same : vertex = source
    · subst vertex
      simpa [initialDistances] using (Path.empty (edge := edge) (source := source))
    · simp [initialDistances, same] at finite
  · intro _ impossible; contradiction
  · intro _ impossible; contradiction
  · intro vertex negative
    by_cases same : vertex = source
    · simp [initialDistances, same] at negative
    · simp [initialDistances, same]
  · intro _ _ _ impossible; contradiction

/-- Queue exhaustion gives the final shortest-path specification. Negative
    results are exactly the canonical `-1` value and exactly the unreachable
    vertices; every finite result is an attained shortest path weight. -/
theorem exhausted_distances_correct (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (invariant : SearchInvariant edge source distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0) :
    ∀ vertex, (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
      (0 ≤ distance vertex → IsShortest edge source vertex (distance vertex)) := by
  intro vertex
  refine ⟨?_, ?_⟩
  · constructor
    · intro unknown
      have notSettled : ¬ settled vertex := by
        intro present
        have finite := invariant.settledFinite vertex present
        omega
      exact exhausted_unreachable edge source distance settled invariant.sourceZero invariant.frontier exhausted vertex notSettled
    · intro unreachable
      by_cases finite : 0 ≤ distance vertex
      · exact False.elim (unreachable _ (invariant.witnesses vertex finite))
      · exact invariant.unknown vertex (by omega)
  · intro finite
    have present : settled vertex := by
      by_cases yes : settled vertex
      · exact yes
      · have unknown := exhausted vertex yes
        omega
    exact ⟨invariant.witnesses vertex finite, invariant.settledOptimal vertex present⟩









/-- An entire scan preserves the same local invariant; its processed list gains
    exactly the scanned edges. This theorem is independent of storage layout. -/
theorem RelaxScan.preserves_invariant (edge : Edges) (source selected : Int)
    (settled : Int → Prop) (edges processed : List (Int × Int)) (distance result : Int → Int)
    (nonnegative : NonnegativeEdges edge)
    (actual : ∀ target weight, (target, weight) ∈ edges → edge selected target weight)
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (scan : RelaxScan settled selected edges distance result) :
    RelaxationInvariant edge source result settled selected (edges.reverse ++ processed) := by
  induction scan generalizing processed with
  | empty => simpa using invariant
  | @skip target weight rest distance result targetSettled tail ih =>
    have next := skip_settled_edge edge source selected target weight distance settled processed
      invariant targetSettled
    have done := ih ((target, weight) :: processed)
      (fun v w member => actual v w (by simp [member])) next
    simpa [List.reverse_cons, List.append_assoc] using done
  | @relax target weight rest distance result targetUnsettled tail ih =>
    have connection := actual target weight (by simp)
    have next := relax_unsettled_edge edge source selected target weight distance settled processed
      invariant connection (nonnegative selected target weight connection) targetUnsettled
    have done := ih ((target, weight) :: processed)
      (fun v w member => actual v w (by simp [member])) next
    simpa [List.reverse_cons, List.append_assoc] using done

/-- Processing the whole outgoing adjacency list restores the ordinary
    outer-loop invariant, ready for the next minimum extraction. -/
theorem RelaxScan.restores_frontier (edge : Edges) (source selected : Int)
    (settled : Int → Prop) (edges : List (Int × Int)) (distance result : Int → Int)
    (nonnegative : NonnegativeEdges edge)
    (represents : ∀ target weight, (target, weight) ∈ edges ↔ edge selected target weight)
    (invariant : RelaxationInvariant edge source distance settled selected [])
    (scan : RelaxScan settled selected edges distance result) :
    SearchInvariant edge source result settled := by
  have done := scan.preserves_invariant edge source selected settled edges [] distance result
    nonnegative (fun target weight member => (represents target weight).mp member) invariant
  apply finish_relaxation edge source selected result settled (edges.reverse ++ []) done
  intro target weight connection
  simpa using (represents target weight).mpr connection











/-- The completed invariant's canonical sentinel removes the nonnegativity
    side condition from the shortest-path interface. -/
theorem shortest_distances_of_canonical (edge : Edges) (source : Int) (distance : Int → Int)
    (canonical : ∀ vertex, distance vertex < 0 → distance vertex = -1)
    (correct : ∀ vertex,
      (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
      (0 ≤ distance vertex → IsShortest edge source vertex (distance vertex))) :
    ShortestDistances edge source distance := by
  intro vertex
  refine ⟨(correct vertex).1, ?_⟩
  intro known
  apply (correct vertex).2
  by_cases nonnegative : 0 ≤ distance vertex
  · exact nonnegative
  · exact False.elim (known (canonical vertex (by omega)))

/-! Backend-independent queue and complete-loop contracts. -/

















/-- Queue implementations share the whole greedy correctness argument, not
    only individual path lemmas. Only the execution-to-`SearchRun` proof changes. -/
theorem SearchRun.correct {edge : Edges} {adjacency : Adjacency}
    {distance output : Int → Int} {settled : Int → Prop} {vertices : List Int} {source : Int}
    (execution : SearchRun edge adjacency distance settled output vertices)
    (nonnegative : NonnegativeEdges edge)
    (invariant : SearchInvariant edge source distance settled) :
    ShortestDistances edge source output := by
  induction execution with
  | done distance settled exhausted =>
    exact shortest_distances_of_canonical edge source distance invariant.unknown
      (exhausted_distances_correct edge source distance settled invariant exhausted)
  | @select distance next output settled selected vertices minimum represents scan rest ih =>
    have started := start_relaxation edge source selected distance settled nonnegative invariant
      minimum.unsettled minimum.finite minimum.minimum
    exact ih (scan.restores_frontier edge source selected _ (adjacency selected) distance next
      nonnegative represents started)

/-- Ordinary initialization is sufficient for every conforming queue backend. -/
theorem SearchRun.initial_correct {edge : Edges} {adjacency : Adjacency} {source : Int}
    {output : Int → Int} {vertices : List Int}
    (execution : SearchRun edge adjacency (initialDistances source) (fun _ => False) output vertices)
    (nonnegative : NonnegativeEdges edge) : ShortestDistances edge source output :=
  execution.correct nonnegative (initial_search_invariant edge source)







end Algo2Lean.Dijkstra

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The finite Dijkstra driver shared by compiled queue backends. It composes
verified local iterations; it does not assume a search transcript, shortest
path correctness, or termination of the whole algorithm.
-/

namespace Algo2Lean.Dijkstra.Execution









/-- The remaining vertex list strictly decreases, so verified local iterations
    suffice for finite compiled execution and the shared `SearchRun` interface. -/
theorem run {State : Type} (api : Interface State) (edge : Edges) (adjacency : Adjacency)
    (progress : ∀ state remaining, api.invariant state remaining →
      Progress api edge adjacency state remaining)
    (state : State) (remaining : List Int) (invariant : api.invariant state remaining) :
    ∃ after, Completed api edge adjacency state after remaining := by
  suffices all : ∀ count state remaining, remaining.length = count → api.invariant state remaining →
      ∃ after, Completed api edge adjacency state after remaining by
    exact all remaining.length state remaining rfl invariant
  intro count
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro state remaining length invariant
    cases progress state remaining invariant with
    | done exhausted complete =>
      exact ⟨state, ⟨remaining, invariant⟩, ⟨[], .done _ _ exhausted, by simp⟩,
        api.weaken (api.zero state) (Nat.zero_le _) (Nat.zero_le _), complete⟩
    | @next after selected iteration =>
      have decreases := remaining_length remaining selected iteration.member
      have smaller : (remaining.erase selected).length < count := by omega
      obtain ⟨final, completed⟩ := ih (remaining.erase selected).length smaller after
        (remaining.erase selected) rfl iteration.next
      obtain ⟨vertices, tail, contained⟩ := completed.search
      have tailRun := tail
      rw [iteration.settled] at tailRun
      have vertexSum : 1 + (remaining.erase selected).length = remaining.length := by omega
      have edgeSum : (adjacency selected).length + edgeBudget adjacency (remaining.erase selected) =
          edgeBudget adjacency remaining := by
        have account := edgeBudget_erase adjacency remaining selected iteration.member
        omega
      refine ⟨final, completed.invariant, ?_, ?_, iteration.continuation final completed.execution⟩
      · refine ⟨selected :: vertices,
          .select iteration.minimum iteration.represents iteration.scan tailRun, ?_⟩
        intro vertex member
        rcases List.mem_cons.mp member with rfl | later
        · exact iteration.member
        · exact List.mem_of_mem_erase (contained vertex later)
      · simpa only [Nat.add_zero, Nat.zero_add, vertexSum, edgeSum] using
          api.compose iteration.cost completed.cost

end Algo2Lean.Dijkstra.Execution

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `dijkstra_correct`: Reusable generic Dijkstra contract.
- `dijkstra_output_exists`: Termination, shortest paths, and queue costs.
- `every_execution`: Correctness and runtime for every execution.
-/

namespace ComposableDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra
open Algo.dijkstra.priority_queue
open PriorityQueueAnalysis

/-! The graph source is imported unchanged. These finite adjacency observations
    use its public interface; all shortest-path mathematics remains shared. -/











theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  induction chain with
  | empty => exact .empty
  | cons edge target weight next tail valid readTarget readWeight readNext nonnegative bound weightBound chain ih =>
    obtain ⟨newValid, targetSame, weightSame, nextSame⟩ := unchanged edge valid
    exact .cons edge target weight next tail newValid (targetSame.trans readTarget)
      (weightSame.trans readWeight) (nextSame.trans readNext) nonnegative bound weightBound ih


theorem AdjacencyChain.member_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges)
    (target weight : Int) (member : (target, weight) ∈ edges) :
    0 ≤ target ∧ target < size ∧ 0 ≤ weight := by
  induction chain with
  | empty => simp at member
  | cons edge first firstWeight next tail valid readTarget readWeight readNext lower upper nonnegative chain ih =>
    simp only [List.mem_cons] at member
    rcases member with same | remaining
    · cases same
      exact ⟨lower, upper, nonnegative⟩
    · exact ih remaining

theorem GraphRep.nonnegative_edges {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    NonnegativeEdges (representedEdges size adjacency) := by
  intro source target weight connection
  obtain ⟨head, _, chain⟩ := representation.chains source connection.1 connection.2.1
  exact (chain.member_valid target weight connection.2.2).2.2








theorem GraphRep.preserved {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep before graph size heads adjacency)
    (frame : GraphFrame before after graph heads) : GraphRep after graph size heads adjacency := by
  refine ⟨frame.valid representation.valid, representation.sizeNonnegative,
    frame.size.trans representation.readSize, frame.headsField.trans representation.readHeads,
    frame.headsValid representation.headsValid, ?_⟩
  intro vertex nonnegative bound
  obtain ⟨head, readHead, chain⟩ := representation.chains vertex nonnegative bound
  exact ⟨head, (frame.entries vertex).trans readHead, chain.preserved frame.edges⟩

theorem graph_frame_write (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (ref : SeqRef) (index value : Int) : GraphFrame heap (heap.write ref index value) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩



theorem graph_frame_tick (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (clock : String) (amount : Nat) : GraphFrame heap (heap.tick clock amount) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩







variable (dependencies : Dependencies)























/-- Initialization adds the source once and enters the main loop. -/
theorem initialize_summary (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (source : Int)
    (queue : ObjectRef) (distance settled : SeqRef)
    (valid : dijkstra.ValidInput dependencies heap (graph,source,queue,distance,settled))
    (inserted : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      ((heap.write distance source 0).tick "queue_updates") (queue,source,0) queuedHeap ())
    (tail : ExtractLoop dependencies queuedHeap graph queue distance settled finalHeap)
    (_distanceAllocated : distance < finalHeap.nextRef) :
    dijkstra.Call dependencies heap (graph,source,queue,distance,settled) finalHeap distance := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.dijkstra_pc29 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.dijkstra_pc28 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc27 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc26 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using inserted.1))
    apply Reaches.prepend (Step.dijkstra_pc25 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc24 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc23 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller inserted.2).trans
    apply Reaches.prepend (Step.dijkstra_pc22 _ _ caller)
    exact tail (.active _ (.fn_dijkstra 7 _) [])
      (by simp [AtExtract, dijkstra.At.extract, dijkstra.Local.graph, dijkstra.Local.queue,
        dijkstra.Local.distance, dijkstra.Local.settled, Config.heap]) caller







variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)



namespace QueueState






end QueueState



theorem Storage.tick {state : QueueState model} (storage : Storage model state) (name : String) :
    Storage model (state.tick model name) :=
  ⟨storage.graph.preserved (graph_frame_tick _ _ _ name 1),
    model.tick storage.queue name 1, storage.distanceAllocated,storage.settledAllocated,storage.separate⟩

theorem Storage.write {state : QueueState model} (storage : Storage model state)
    (ref : SeqRef) (index value : Int) (member : ref ∈ client.protection.sequences) :
    Storage model (state.write model ref index value) :=
  ⟨storage.graph.preserved (graph_frame_write _ _ _ ref index value),
    model.write storage.queue ref member index value,
    storage.distanceAllocated,storage.settledAllocated,storage.separate⟩

/-- The generic queue frame implies preservation of the imported graph. -/
theorem graph_frame_of_protected {before after : Heap}
    (representation : GraphRep before client.graph client.size client.heads client.adjacency)
    (frame : PriorityQueueAnalysis.Frame client.protection before after) :
    GraphFrame before after client.graph client.heads := by
  have validGraph : is_Graph after client.graph :=
    ⟨Nat.lt_of_lt_of_le representation.valid.1 frame.nextObject,
      (frame.classes _ representation.valid.1).trans representation.valid.2⟩
  have graphFields : after.objects client.graph = before.objects client.graph :=
    frame.objects _ "graph.Graph" representation.valid.1 representation.valid.2 (by simp [Client.protection])
  have graphRead : ∀ field, after.readField client.graph field = before.readField client.graph field := by
    intro field
    simp [Heap.readField,graphFields]
  have oldHeads : client.heads < before.nextCollection := representation.headsValid.1
  have headsType : after.sequenceType client.heads = before.sequenceType client.heads := frame.types _ oldHeads
  have headsValid : seq_Edge_optional.valid after client.heads :=
    ⟨Nat.lt_of_lt_of_le oldHeads frame.nextCollection, headsType.trans representation.headsValid.2⟩
  have collections := frame.collections _ (by simp [Client.protection]) oldHeads
  have entries : ∀ vertex, seq_Edge_optional.get after client.heads vertex =
      seq_Edge_optional.get before client.heads vertex := by
    intro vertex
    simp [SequenceType.get,headsValid,representation.headsValid,Heap.readElement,collections]
  refine ⟨fun _ => validGraph, ?_, ?_, fun _ => headsValid, entries, ?_⟩
  · simp [field_Graph_size, validGraph,representation.valid,graphRead]
  · simp [field_Graph_heads, validGraph,representation.valid,graphRead]
  · intro ref valid
    have newValid : is_Edge after ref :=
      ⟨Nat.lt_of_lt_of_le valid.1 frame.nextObject, (frame.classes _ valid.1).trans valid.2⟩
    have fields := frame.objects ref "graph.Edge" valid.1 valid.2 (by simp [Client.protection])
    have reads : ∀ field, after.readField ref field = before.readField ref field := by
      intro field
      simp [Heap.readField,fields]
    exact ⟨newValid, by simp [field_Edge_target,valid,newValid,reads],
      by simp [field_Edge_weight,valid,newValid,reads],
      by simp [field_Edge_next,valid,newValid,reads]⟩

theorem Storage.preserved {before after : QueueState model} (storage : Storage model before)
    (rep : model.Rep after.heap after.queueState)
    (frame : PriorityQueueAnalysis.Frame client.protection before.heap after.heap) :
    Storage model after :=
  ⟨storage.graph.preserved (graph_frame_of_protected storage.graph frame),rep,
    Nat.lt_of_lt_of_le storage.distanceAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.settledAllocated frame.nextRef,storage.separate⟩

















variable (contracts : Contracts model reservedClocks)
include contracts

theorem work_tick_left (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model (before.tick name) after = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]

theorem work_tick_right (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model before (after.tick name) = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]





theorem queue_update (state : QueueState model) (vertex key : Int) (storage : Storage model state)
    (lower : 0 ≤ vertex) (upper : vertex < model.capacity)
    (improves : ∀ old, (vertex,old) ∈ state.entries model → key < old) :
    ∃ after, QueueUpdated model state after vertex key := by
  obtain ⟨heap,next,effect⟩ := contracts.update state.heap state.queueState vertex key storage.queue lower upper improves
  exact ⟨⟨heap,next⟩,effect.execution,storage.preserved model effect.represented effect.frame,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.distanceAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.settledAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩





















/-- Termination and the logical search run are obtained from local queue contracts,
    by the existing finite driver, without any assumed whole-program execution. -/
theorem extraction_loop (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining) :
    ∃ after, Algo2Lean.Dijkstra.Execution.Completed (executionInterface model)
      (representedEdges client.size client.adjacency) client.adjacency state after remaining :=
  Algo2Lean.Dijkstra.Execution.run (executionInterface model)
    (representedEdges client.size client.adjacency) client.adjacency
    (extraction_progress model contracts capacity) state remaining invariant



/-- The generic algorithm terminates and computes shortest distances. Queue
    assumptions concern individual calls only. The same calls establish its
    operation counts and backend-weighted amortized bound. -/
theorem dijkstra_complete (capacity : client.size ≤ model.capacity)
    (before : QueueState model) (source : Int) (storage : Storage model before)
    (empty : before.entries model = [])
    (distances : before.heap.read client.distance = fun _ => -1)
    (flags : before.heap.read client.settled = fun _ => 0)
    (sourceLower : 0 ≤ source) (sourceUpper : source < client.size) :
    ∃ after,
      dijkstra.Call dependencies before.heap
        (client.graph,source,client.queue,client.distance,client.settled) after client.distance ∧
      GraphRep after client.graph client.size client.heads client.adjacency ∧
      ShortestDistances (representedEdges client.size client.adjacency) source (after.read client.distance) ∧
      OperationCounts before.heap after client.size.toNat (edgeBudget client.adjacency (vertexRange client.size)) ∧
      work model before.heap after ≤ before.potential model +
        model.updateBudget * (edgeBudget client.adjacency (vertexRange client.size) + 1) +
        model.popBudget * client.size.toNat ∧ client.distance < after.nextRef ∧
      client.caller.Footprint after [] [] [] := by
  let prepared := (before.write model client.distance source 0).tick model "queue_updates"
  have preparedStorage : Storage model prepared :=
    (storage.write model _ source 0 (by simp [Client.protection])).tick model "queue_updates"
  obtain ⟨initial,inserted⟩ := queue_update model contracts prepared source 0 preparedStorage sourceLower
    (by omega) (by intro key member; change (source,key) ∈ before.entries model at member; simp [empty] at member)
  have initialDistances : initial.heap.read client.distance = Algo2Lean.Dijkstra.initialDistances source := by
    rw [inserted.distance]
    funext vertex
    change (before.heap.write client.distance source 0).read client.distance vertex = _
    simpa [Heap.read,Heap.write,Algo2Lean.Dijkstra.initialDistances] using
      congrArg (fun value => if vertex = source then 0 else value) (congrFun distances vertex)
  have initialFlags : initial.heap.read client.settled = fun _ => 0 := by
    rw [inserted.settled]
    funext vertex
    change (before.heap.write client.distance source 0).read client.settled vertex = _
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (Ne.symm storage.separate)]
    exact congrFun flags vertex
  have invariant : LoopInvariant model initial (vertexRange client.size) := by
    refine ⟨inserted.storage, ?_, ?_, vertexRange_nodup client.size, ?_⟩
    · intro vertex key
      rw [inserted.contents,initialDistances,initialFlags]
      change (vertex = source ∧ key = 0) ∨ (vertex ≠ source ∧ (vertex,key) ∈ before.entries model) ↔ _
      by_cases same : vertex = source <;>
        simp [empty,Algo2Lean.Dijkstra.initialDistances,same]
    · intro vertex finite
      rw [initialDistances] at finite
      by_cases same : vertex = source
      · simpa [same] using And.intro sourceLower sourceUpper
      · simp [Algo2Lean.Dijkstra.initialDistances,same] at finite
    · intro vertex
      rw [initialFlags]
      simp
  obtain ⟨after,completed⟩ := extraction_loop model contracts capacity initial (vertexRange client.size) invariant
  obtain ⟨pending,finalInvariant⟩ := completed.invariant
  change LoopInvariant model after pending at finalInvariant
  obtain ⟨vertices,search,contained⟩ := completed.search
  change SearchRun (representedEdges client.size client.adjacency) client.adjacency
    (initial.heap.read client.distance) (fun vertex => initial.heap.read client.settled vertex ≠ 0)
    (after.heap.read client.distance) vertices at search
  rw [initialDistances,initialFlags] at search
  simp only [ne_self_iff_false] at search
  have correct := search.initial_correct storage.graph.nonnegative_edges
  have bounds : CostBounds model initial after client.size.toNat
      (edgeBudget client.adjacency (vertexRange client.size)) := by
    simpa only [vertexRange_length] using! completed.cost
  have initialClocks (name) (member : name ∈ reservedClocks) := inserted.bookkeeping name member
  refine ⟨after.heap.tick "queue_empty_checks", ?_,
    finalInvariant.storage.graph.preserved (graph_frame_tick _ _ _ "queue_empty_checks" 1),correct,?_,?_,
    finalInvariant.storage.distanceAllocated,
    (model.callerPreserved finalInvariant.storage.queue).tick "queue_empty_checks"⟩
  · exact initialize_summary dependencies before.heap initial.heap (after.heap.tick "queue_empty_checks")
      client.graph source client.queue client.distance client.settled
      ⟨storage.graph.valid,model.valid storage.queue,storage.distanceAllocated,storage.settledAllocated⟩
      inserted.execution completed.execution.1 completed.execution.2
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have clocks := initialClocks "queue_updates" (by simp [reservedClocks])
      have count := bounds.updates
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_pops" (by simp [reservedClocks])
      have count := bounds.pops
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_empty_checks" (by simp [reservedClocks])
      have count := bounds.checks
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "edges" (by simp [reservedClocks])
      have count := bounds.visits
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "improvements" (by simp [reservedClocks])
      have count := bounds.improvements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "settlements" (by simp [reservedClocks])
      have count := bounds.settlements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
  · have initialBound := inserted.amortized
    change work model ((before.heap.write client.distance source 0).tick "queue_updates") initial.heap + _ ≤ _ at initialBound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at initialBound
    change work model before.heap initial.heap + initial.potential model ≤ before.potential model + model.updateBudget at initialBound
    have finalBound := bounds.amortized
    have triangle := work_triangle model before.heap initial.heap after.heap
    rw [work_tick_right model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])]
    simp only [Nat.mul_add,Nat.mul_one]
    omega





-- Main result: Correctness and running time


end ComposableDijkstraAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {dependencies : Algo.dijkstra.dijkstra.Dependencies} {client : ComposableDijkstraAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model ComposableDijkstraAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (before : ComposableDijkstraAnalysis.QueueState model) (source : Int),
            ComposableDijkstraAnalysis.Storage model before →
              Eq.{1} (ComposableDijkstraAnalysis.QueueState.entries model before) List.nil.{0} →
                (Eq.{1} (before.heap.read client.distance) fun x => (-1 : Int)) →
                  (Eq.{1} (before.heap.read client.settled) fun x => (0 : Int)) →
                    LE.le.{0} (0 : Int) source →
                      LT.lt.{0} source client.size →
                        Exists.{1} fun after =>
                          Algo.dijkstra.dijkstra.dijkstra.Call dependencies before.heap
                              (Prod.mk.{0, 0} client.graph
                                (Prod.mk.{0, 0} source
                                  (Prod.mk.{0, 0} client.queue
                                    (Prod.mk.{0, 0} client.distance client.settled))))
                              after client.distance ∧
                            ComposableDijkstraAnalysis.GraphRep after client.graph client.size
                                client.heads client.adjacency ∧
                              Algo2Lean.Dijkstra.ShortestDistances
                                  (Algo2Lean.Dijkstra.representedEdges client.size client.adjacency)
                                  source (after.read client.distance) ∧
                                ComposableDijkstraAnalysis.OperationCounts before.heap after
                                    client.size.toNat
                                    (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                      (Algo2Lean.Dijkstra.vertexRange client.size)) ∧
                                  LE.le.{0} (ComposableDijkstraAnalysis.work model before.heap after)
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (ComposableDijkstraAnalysis.QueueState.potential model before)
                                          (HMul.hMul.{0, 0, 0} model.updateBudget
                                            (HAdd.hAdd.{0, 0, 0}
                                              (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                                (Algo2Lean.Dijkstra.vertexRange client.size))
                                              (1 : Nat))))
                                        (HMul.hMul.{0, 0, 0} model.popBudget client.size.toNat)) ∧
                                    LT.lt.{0} client.distance after.nextRef ∧
                                      client.caller.Footprint after List.nil.{0} List.nil.{0}
                                        List.nil.{0} :=
  ComposableDijkstraAnalysis.dijkstra_complete
