-- Prove2me | solution 1 for DRCVRP.RCI.rvrp_equiv_twoIndexFlow
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T05:18:41.476897+00:00
-- url     : https://prove2.me/submissions/0866c633-f871-49dd-8735-945fda3ede1f

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations

open MeasureTheory

set_option autoImplicit false


/- Inlined checked module: CheckedChanceBridge -/
section
-- Adapted from the two accepted proofs by @ryanshin in the official Prove2Me export.
-- https://prove2.me/submissions/76d136f9-9592-49c5-b254-18aafb413f43
-- https://prove2.me/submissions/96c68a07-6e2c-4a8f-b05f-5cb29539478f
-- The shared CDF proof is identical in both originals. Only namespace/theorem names
-- and the proof-local have spelling are changed for this strict combined module.

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace DRCVRP.RCI.Checked

theorem var_iff{Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (τ : ℝ) :
    ENNReal.ofReal α ≤ P {q | X q ≤ τ} ↔ MultistageStochastic.valueAtRisk P X α ≤ τ := by
  have : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map hX.aemeasurable
  let F := cdf (P.map X)
  have hf (y : ℝ) : ENNReal.ofReal α ≤ P {q | X q ≤ y} ↔ α ≤ F y := by
    change ENNReal.ofReal α ≤ P (X ⁻¹' Iic y) ↔ α ≤ F y
    rw [← Measure.map_apply hX measurableSet_Iic, ← ofReal_cdf]
    exact ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)
  have heq : {y : ℝ | ENNReal.ofReal α ≤ P {q | X q ≤ y}} = {y : ℝ | α ≤ F y} := by
    ext y
    exact hf y
  let S := {y : ℝ | α ≤ F y}
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop (P.map X)).eventually (eventually_gt_nhds hα1)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (P.map X)).eventually (eventually_lt_nhds hα0)).exists
    refine ⟨y, fun z hz => ?_⟩
    by_contra h
    have hzy : z ≤ y := le_of_not_ge h
    have hh := F.mono hzy
    exact (not_lt_of_ge (hz.trans hh)) hy
  have hmem : α ≤ F (sInf S) := by
    have hlim : Tendsto F (𝓝[>] sInf S) (𝓝 (F (sInf S))) :=
      (F.right_continuous _).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact hz.trans (F.mono hzy.le)
  rw [hf, MultistageStochastic.valueAtRisk, heq]
  exact ⟨fun h => csInf_le hb h, fun h => hmem.trans (F.mono h)⟩

theorem prob_le_iff_valueAtRisk_le{n : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (X : (Fin n → ℝ) → ℝ) (hX : Measurable X) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (τ : ℝ) :
    ENNReal.ofReal (1 - ε) ≤ P {q | X q ≤ τ} ↔
      MultistageStochastic.valueAtRisk P X (1 - ε) ≤ τ :=
  var_iff P X hX (1-ε) (by linarith) (by linarith) τ

theorem chance_constraint_iff_worstCaseVaR_le{n : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (hne : Amb.Nonempty)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (Q : ℝ) (r : List (Fin n)) (hr : r.Nodup)
    (hbdd : BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε)) '' Amb)) :
    (RouteChanceFeasible Amb ε Q r ↔
      ∀ P ∈ Amb, MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε) ≤ Q) ∧
    (RouteChanceFeasible Amb ε Q r ↔ worstCaseVaR Amb ε r.toFinset ≤ Q) := by
  have heq (q : Fin n → ℝ) : (r.map q).sum = ∑ i ∈ r.toFinset, q i := by
    exact (List.sum_toFinset _ hr).symm
  have hfirst : RouteChanceFeasible Amb ε Q r ↔
      ∀ P ∈ Amb, MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ r.toFinset, q i) (1-ε) ≤ Q := by
    unfold RouteChanceFeasible
    simp only [heq]
    apply forall₂_congr
    intro P hP
    have := hAmb P hP
    exact var_iff P _ (by fun_prop) (1-ε) (by linarith) (by linarith) Q
  refine ⟨hfirst, hfirst.trans ?_⟩
  unfold worstCaseVaR
  constructor
  · intro h
    apply csSup_le (hne.image _)
    rintro y ⟨P,hP,rfl⟩
    exact h P hP
  · intro h P hP
    exact (le_csSup hbdd ⟨P,hP,rfl⟩).trans h

end DRCVRP.RCI.Checked
end
end


/- Inlined checked module: DemandChanceBounds -/
section
open MeasureTheory

namespace DRCVRP.RCI.Checked

theorem demandEstimator_empty {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (eps Q : ℝ) :
    demandEstimator Amb eps Q ∅ = 0 := by simp [demandEstimator]

theorem demandEstimator_ge_one {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (eps Q : ℝ)
    {S : Finset (Fin n)} (hS : S.Nonempty) : 1 ≤ demandEstimator Amb eps Q S := by
  simpa only [demandEstimator, if_neg hS.ne_empty] using
    (le_max_right ⌈worstCaseVaR Amb eps S / Q⌉ (1 : ℤ))

theorem estimator_le_one_iff {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (eps Q : ℝ)
    (hQ : 0 < Q) {S : Finset (Fin n)} (hS : S.Nonempty) :
    demandEstimator Amb eps Q S ≤ 1 ↔ worstCaseVaR Amb eps S ≤ Q := by
  simp only [demandEstimator, if_neg hS.ne_empty, max_le_iff, le_refl, and_true,
    Int.ceil_le, Int.cast_one, div_le_one₀ hQ]

theorem route_chance_iff_estimator {n : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (eps Q : ℝ)
    (he0 : 0 < eps) (he1 : eps < 1) (hQ : 0 < Q)
    (r : List (Fin n)) (hr : r.Nodup) (hrne : r ≠ [])
    (hbdd : BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ r.toFinset, q i) (1 - eps)) '' Amb)) :
    RouteChanceFeasible Amb eps Q r ↔ demandEstimator Amb eps Q r.toFinset ≤ 1 := by
  have hS : r.toFinset.Nonempty := by simpa using hrne
  rw [estimator_le_one_iff Amb eps Q hQ hS]
  by_cases hne : Amb.Nonempty
  · exact (chance_constraint_iff_worstCaseVaR_le Amb hAmb hne eps he0 he1 Q r hr hbdd).2
  · have hempty : Amb = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, RouteChanceFeasible, worstCaseVaR, hQ.le]

theorem subset_route_estimator_le_one {n : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (eps Q : ℝ)
    (he0 : 0 < eps) (he1 : eps < 1) (hQ : 0 < Q)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (r : List (Fin n)) (hr : r.Nodup) (hchance : RouteChanceFeasible Amb eps Q r)
    (S : Finset (Fin n)) (hSr : S ⊆ r.toFinset) :
    demandEstimator Amb eps Q S ≤ 1 := by
  by_cases hS : S.Nonempty
  · rw [estimator_le_one_iff Amb eps Q hQ hS]
    by_cases hne : Amb.Nonempty
    · unfold worstCaseVaR
      apply csSup_le (hne.image _)
      rintro z ⟨P, hP, rfl⟩
      have : IsProbabilityMeasure P := hAmb P hP
      apply (var_iff P (fun q => ∑ i ∈ S, q i) (by fun_prop)
        (1 - eps) (by linarith) (by linarith) Q).mp
      apply (hchance P hP).trans
      apply measure_mono_ae
      filter_upwards [hnonneg P hP] with q hq
      intro hqQ
      have hsum : (∑ i ∈ S, q i) ≤ ∑ i ∈ r.toFinset, q i :=
        Finset.sum_le_sum_of_subset_of_nonneg hSr (fun i _ _ => hq i)
      have heq : (r.map q).sum = ∑ i ∈ r.toFinset, q i :=
        (List.sum_toFinset _ hr).symm
      exact hsum.trans (heq ▸ hqQ)
    · have hempty : Amb = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simpa [hempty, worstCaseVaR] using hQ.le
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hempty, demandEstimator]

theorem estimator_biUnion_le_sum {n : ℕ} {I : Type*} [DecidableEq I]
    (Amb : Set (Measure (Fin n → ℝ))) (eps Q : ℝ) (hsub : IsSubadditive Amb eps Q)
    (T : Finset I) (sets : I → Finset (Fin n)) :
    demandEstimator Amb eps Q (T.biUnion sets) ≤ ∑ i ∈ T, demandEstimator Amb eps Q (sets i) := by
  induction T using Finset.induction_on with
  | empty => simp [demandEstimator]
  | @insert i T hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (hsub (sets i) (T.biUnion sets)).trans (add_le_add le_rfl ih)

end DRCVRP.RCI.Checked
end


/- Inlined checked module: RouteArcFacts -/
section
namespace DRCVRP.RCI.Checked

def chainEdges {V : Type*} (terminal : V) : V → List V → List (V × V)
  | a, [] => [(a, terminal)]
  | a, b :: l => (a, b) :: chainEdges terminal b l

theorem chainEdges_zip {V : Type*} (terminal a : V) (l : List V) :
    (a :: (l ++ [terminal])).zip (l ++ [terminal]) = chainEdges terminal a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simpa only [List.cons_append, List.zip_cons_cons, chainEdges] using congrArg ((a, b) :: ·) (ih b)

theorem chainEdges_fst {V : Type*} (terminal a : V) (l : List V) :
    (chainEdges terminal a l).map Prod.fst = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [chainEdges, List.map_cons, ih]

theorem chainEdges_snd {V : Type*} (terminal a : V) (l : List V) :
    (chainEdges terminal a l).map Prod.snd = l ++ [terminal] := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [chainEdges, List.map_cons, ih, List.cons_append]

theorem chainEdges_irrefl {V : Type*} (terminal a : V) (l : List V)
    (hn : (a :: l).Nodup) (ht : terminal ∉ l) (he : l = [] → a ≠ terminal) :
    ∀ e ∈ chainEdges terminal a l, e.1 ≠ e.2 := by
  induction l generalizing a with
  | nil => simpa only [chainEdges, List.mem_singleton, forall_eq] using he rfl
  | cons b l ih =>
    intro e hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact fun hab => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl hab))
    · apply ih b (List.nodup_cons.mp hn).2 (fun h => ht (List.mem_cons_of_mem _ h))
        (fun _ hbt => ht (by simp [hbt])) e hmem

theorem routeArcs_chain {n : ℕ} (r : List (Fin n)) :
    routeArcs r = chainEdges (0 : Fin (n + 1)) 0 (r.map Fin.succ) := by
  change (0 :: (r.map Fin.succ ++ [0])).zip (r.map Fin.succ ++ [0]) = _
  exact chainEdges_zip _ _ _

theorem routeArcs_fst {n : ℕ} (r : List (Fin n)) :
    (routeArcs r).map Prod.fst = 0 :: r.map Fin.succ := by
  rw [routeArcs_chain, chainEdges_fst]

theorem routeArcs_snd {n : ℕ} (r : List (Fin n)) :
    (routeArcs r).map Prod.snd = r.map Fin.succ ++ [0] := by
  rw [routeArcs_chain, chainEdges_snd]

theorem routeArcs_nodup {n : ℕ} (r : List (Fin n)) (hr : r.Nodup) :
    (routeArcs r).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [routeArcs_fst, List.nodup_cons]
  exact ⟨by simp, hr.map (Fin.succ_injective n)⟩

theorem routeArcs_irrefl {n : ℕ} (r : List (Fin n)) (hr : r.Nodup) (he : r ≠ []) :
    ∀ e ∈ routeArcs r, e.1 ≠ e.2 := by
  rw [routeArcs_chain]
  apply chainEdges_irrefl
  · exact List.nodup_cons.mpr ⟨by simp, hr.map (Fin.succ_injective n)⟩
  · simp
  · intro h
    have : r = [] := List.map_eq_nil_iff.mp h
    exact (he this).elim

theorem routeSet_flat_nodup {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R) :
    ((List.ofFn R).flatten).Nodup := hR.2.symm.nodup (List.nodup_finRange n)

theorem routeSet_nodup {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (k : Fin m) : (R k).Nodup :=
  (List.nodup_flatten.mp (routeSet_flat_nodup hR)).1 _ (List.mem_ofFn.mpr ⟨k, rfl⟩)

theorem routeSet_disjoint {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    {k l : Fin m} (hkl : k ≠ l) : List.Disjoint (R k) (R l) := by
  have hd := List.pairwise_ofFn.mp (List.nodup_flatten.mp (routeSet_flat_nodup hR)).2
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hd h
  · exact (hd h).symm

theorem routeSet_covers {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (j : Fin n) : ∃ k, j ∈ R k := by
  have hj : j ∈ (List.ofFn R).flatten := hR.2.mem_iff.mpr (List.mem_finRange j)
  obtain ⟨r, hr, hj⟩ := List.mem_flatten.mp hj
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨k, hj⟩

def allRouteArcs {n m : ℕ} (R : Fin m → List (Fin n)) : List (Fin (n + 1) × Fin (n + 1)) :=
  (List.ofFn fun k => routeArcs (R k)).flatten

theorem mem_allRouteArcs {n m : ℕ} (R : Fin m → List (Fin n)) (e : Fin (n + 1) × Fin (n + 1)) :
    e ∈ allRouteArcs R ↔ ∃ k, e ∈ routeArcs (R k) := by
  simp only [allRouteArcs, List.mem_flatten, List.mem_ofFn]
  aesop

theorem inducedFlow_eq_mem {n m : ℕ} (R : Fin m → List (Fin n)) (i j : Fin (n + 1)) :
    inducedFlow R i j = if (i, j) ∈ allRouteArcs R then 1 else 0 := by
  simp only [inducedFlow, mem_allRouteArcs]

end DRCVRP.RCI.Checked
end


/- Inlined checked module: RouteArcSum -/
section
namespace DRCVRP.RCI.Checked

theorem routeArc_source_mem {n : ℕ} {r : List (Fin n)} {e : Fin (n + 1) × Fin (n + 1)}
    (he : e ∈ routeArcs r) (hi : e.1 ≠ 0) : ∃ a ∈ r, a.succ = e.1 := by
  have hm : e.1 ∈ (routeArcs r).map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [routeArcs_fst] at hm
  rcases List.mem_cons.mp hm with h | h
  · exact (hi h).elim
  · exact List.mem_map.mp h

theorem routeArc_target_mem {n : ℕ} {r : List (Fin n)} {e : Fin (n + 1) × Fin (n + 1)}
    (he : e ∈ routeArcs r) (hj : e.2 ≠ 0) : ∃ a ∈ r, a.succ = e.2 := by
  have hm : e.2 ∈ (routeArcs r).map Prod.snd := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [routeArcs_snd] at hm
  rcases List.mem_append.mp hm with h | h
  · exact List.mem_map.mp h
  · exact (hj (List.mem_singleton.mp h)).elim

theorem routeArcs_disjoint {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    {k l : Fin m} (hkl : k ≠ l) : List.Disjoint (routeArcs (R k)) (routeArcs (R l)) := by
  apply List.disjoint_left.mpr
  intro e hek hel
  by_cases hi : e.1 = 0
  · have hj : e.2 ≠ 0 := fun h =>
      routeArcs_irrefl (R k) (routeSet_nodup hR k) (hR.1 k) e hek (hi.trans h.symm)
    obtain ⟨a, ha, hea⟩ := routeArc_target_mem hek hj
    obtain ⟨b, hb, heb⟩ := routeArc_target_mem hel hj
    have hab : a = b := Fin.succ_injective n (hea.trans heb.symm)
    subst b
    exact List.disjoint_left.mp (routeSet_disjoint hR hkl) ha hb
  · obtain ⟨a, ha, hea⟩ := routeArc_source_mem hek hi
    obtain ⟨b, hb, heb⟩ := routeArc_source_mem hel hi
    have hab : a = b := Fin.succ_injective n (hea.trans heb.symm)
    subst b
    exact List.disjoint_left.mp (routeSet_disjoint hR hkl) ha hb

theorem allRouteArcs_nodup {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R) :
    (allRouteArcs R).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
    exact routeArcs_nodup _ (routeSet_nodup hR k)
  · apply List.pairwise_ofFn.mpr
    intro k l hkl
    exact routeArcs_disjoint hR (ne_of_lt hkl)

theorem allRouteArcs_irrefl {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R) :
    ∀ e ∈ allRouteArcs R, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨k, hk⟩ := (mem_allRouteArcs R e).mp he
  exact routeArcs_irrefl (R k) (routeSet_nodup hR k) (hR.1 k) e hk

theorem inducedFlow_diag {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) : inducedFlow R i i = 0 := by
  rw [inducedFlow_eq_mem]
  exact if_neg (fun h => allRouteArcs_irrefl hR (i, i) h rfl)

theorem indicator_sum_eq_list_sum {A B : Type*} [Fintype A] [DecidableEq A]
    [BEq A] [LawfulBEq A] [AddCommMonoid B] (l : List A) (hl : l.Nodup) (f : A → B) :
    (∑ a, if a ∈ l then f a else 0) = (l.map f).sum := by
  rw [← Finset.sum_filter]
  have heq : Finset.univ.filter (fun a => a ∈ l) = l.toFinset := by ext a; simp
  rw [heq]
  exact List.sum_toFinset _ hl

theorem allRouteArcs_sum {n m : ℕ} {A : Type*} [AddCommMonoid A]
    (R : Fin m → List (Fin n)) (f : Fin (n + 1) × Fin (n + 1) → A) :
    ((allRouteArcs R).map f).sum = ∑ k, ((routeArcs (R k)).map f).sum := by
  simp only [allRouteArcs, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem flow_weight_sum_eq {n m : ℕ} {A : Type*} [AddCommMonoid A]
    {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (w : Fin (n + 1) → Fin (n + 1) → A) :
    (∑ i, ∑ j, inducedFlow R i j • w i j) =
      ∑ k, ((routeArcs (R k)).map (fun e => w e.1 e.2)).sum := by
  simp_rw [inducedFlow_eq_mem, ite_smul, one_smul, zero_smul]
  rw [← Fintype.sum_prod_type (fun e : Fin (n + 1) × Fin (n + 1) =>
    if e ∈ allRouteArcs R then w e.1 e.2 else 0)]
  exact (indicator_sum_eq_list_sum _ (allRouteArcs_nodup hR) (fun e => w e.1 e.2)).trans
    (allRouteArcs_sum _ _)

theorem routeSet_flow_cost {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ) :
    flowCost c (inducedFlow R) = routeSetCost c R := by
  have hs := flow_weight_sum_eq hR c
  have he : flowCost c (inducedFlow R) = ∑ i, ∑ j, inducedFlow R i j • c i j := by
    unfold flowCost
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≠ i
    · simp [hj, nsmul_eq_mul, mul_comm]
    · have heq : j = i := not_ne_iff.mp hj
      subst j
      simp [inducedFlow_diag hR]
  exact he.trans hs

end DRCVRP.RCI.Checked
end


/- Inlined checked module: RouteDegrees -/
section
namespace DRCVRP.RCI.Checked

theorem list_indicator_sum {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A]
    (l : List A) (a : A) :
    (l.map (fun b => if b = a then (1 : ℕ) else 0)).sum = l.count a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · simp [h, ih, Nat.add_comm]
    · simp [h, ih]

theorem routeArcs_source_sum {n : ℕ} (r : List (Fin n)) (i : Fin (n + 1)) :
    ((routeArcs r).map (fun e => if e.1 = i then (1 : ℕ) else 0)).sum =
      (0 :: r.map Fin.succ).count i := by
  rw [← routeArcs_fst r]
  simpa only [List.map_map, Function.comp_def] using
    list_indicator_sum ((routeArcs r).map Prod.fst) i

theorem routeArcs_target_sum {n : ℕ} (r : List (Fin n)) (i : Fin (n + 1)) :
    ((routeArcs r).map (fun e => if e.2 = i then (1 : ℕ) else 0)).sum =
      (r.map Fin.succ ++ [0]).count i := by
  rw [← routeArcs_snd r]
  simpa only [List.map_map, Function.comp_def] using
    list_indicator_sum ((routeArcs r).map Prod.snd) i

theorem routeSet_count_sum {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (j : Fin n) : (∑ k, (R k).count j) = 1 := by
  have h : ((List.ofFn R).flatten).count j = 1 := by
    rw [hR.2.count_eq]
    exact List.count_finRange j
  simpa only [List.count_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h

theorem source_count_sum {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) : (∑ k, (0 :: (R k).map Fin.succ).count i) = nodeDegree m i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz (k : Fin m) : ((R k).map Fin.succ).count 0 = 0 :=
      List.count_eq_zero_of_not_mem (by simp)
    simp [nodeDegree, hz]
  · have hz : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    simpa only [List.count_cons_of_ne hz,
      List.count_map_of_injective _ Fin.succ (Fin.succ_injective n),
      nodeDegree, if_neg (Fin.succ_ne_zero j)] using routeSet_count_sum hR j

theorem target_count_sum {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) : (∑ k, ((R k).map Fin.succ ++ [0]).count i) = nodeDegree m i := by
  have heq (l : List (Fin (n + 1))) : (l ++ [0]).count i = (0 :: l).count i := by
    simp [List.count_append, List.count_cons]
  simp_rw [heq]
  exact source_count_sum hR i

theorem inducedFlow_out_sum {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) : (∑ j, inducedFlow R i j) = nodeDegree m i := by
  have hw := flow_weight_sum_eq hR (fun a _ => if a = i then (1 : ℕ) else 0)
  have hl : (∑ a, ∑ b, inducedFlow R a b • (if a = i then (1 : ℕ) else 0)) =
      ∑ b, inducedFlow R i b := by
    simp [mul_ite, Finset.sum_ite_irrel]
  rw [hl] at hw
  simp_rw [routeArcs_source_sum] at hw
  exact hw.trans (source_count_sum hR i)

theorem inducedFlow_in_sum {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) : (∑ j, inducedFlow R j i) = nodeDegree m i := by
  have hw := flow_weight_sum_eq hR (fun _ b => if b = i then (1 : ℕ) else 0)
  have hl : (∑ a, ∑ b, inducedFlow R a b • (if b = i then (1 : ℕ) else 0)) =
      ∑ a, inducedFlow R a i := by
    simp [mul_ite]
  rw [hl] at hw
  simp_rw [routeArcs_target_sum] at hw
  exact hw.trans (target_count_sum hR i)

theorem inducedFlow_out_degree {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i), inducedFlow R i j) = nodeDegree m i := by
  rw [Finset.sum_filter]
  convert inducedFlow_out_sum hR i using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · subst j; simp [inducedFlow_diag hR]
  · simp [h]

theorem inducedFlow_in_degree {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (i : Fin (n + 1)) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i), inducedFlow R j i) = nodeDegree m i := by
  rw [Finset.sum_filter]
  convert inducedFlow_in_sum hR i using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · subst j; simp [inducedFlow_diag hR]
  · simp [h]

end DRCVRP.RCI.Checked
end


/- Inlined checked module: RouteCutFacts -/
section
namespace DRCVRP.RCI.Checked

def edgeCut {V : Type*} [DecidableEq V] (S : Finset V) (e : V × V) : ℕ :=
  if e.1 ∉ S ∧ e.2 ∈ S then 1 else 0

def routeCut {n : ℕ} (S : Finset (Fin n)) (r : List (Fin n)) : ℕ :=
  ((routeArcs r).map (edgeCut (customerNodes S))).sum

theorem chain_cut_none {V : Type*} [DecidableEq V] (S : Finset V) (terminal a : V)
    (l : List V) (ht : terminal ∉ S) (hl : ∀ v ∈ l, v ∉ S) :
    ((chainEdges terminal a l).map (edgeCut S)).sum = 0 := by
  induction l generalizing a with
  | nil => simp [chainEdges, edgeCut, ht]
  | cons b l ih =>
    have hb := hl b (by simp)
    have htail : ∀ v ∈ l, v ∉ S := fun v hv => hl v (List.mem_cons_of_mem _ hv)
    simp [chainEdges, edgeCut, hb, ih b htail]

theorem chain_cut_all {V : Type*} [DecidableEq V] (S : Finset V) (terminal a : V)
    (l : List V) (ht : terminal ∉ S) (hl : ∀ v ∈ l, v ∈ S) :
    ((chainEdges terminal a l).map (edgeCut S)).sum = if a ∉ S ∧ l ≠ [] then 1 else 0 := by
  induction l generalizing a with
  | nil => simp [chainEdges, edgeCut, ht]
  | cons b l ih =>
    have hb := hl b (by simp)
    have htail : ∀ v ∈ l, v ∈ S := fun v hv => hl v (List.mem_cons_of_mem _ hv)
    simp [chainEdges, edgeCut, hb, ih b htail]

theorem chain_cut_ge_one {V : Type*} [DecidableEq V] (S : Finset V) (terminal a : V)
    (l : List V) (ha : a ∉ S) (hl : ∃ v ∈ l, v ∈ S) :
    1 ≤ ((chainEdges terminal a l).map (edgeCut S)).sum := by
  induction l generalizing a with
  | nil => obtain ⟨v, hv, _⟩ := hl; cases hv
  | cons b l ih =>
    by_cases hb : b ∈ S
    · simp [chainEdges, edgeCut, ha, hb]
    · have htail : ∃ v ∈ l, v ∈ S := by
        obtain ⟨v, hv, hvs⟩ := hl
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (hb hvs).elim
        · exact ⟨v, hv, hvs⟩
      have ht := ih b hb htail
      simpa [chainEdges, edgeCut, hb] using ht

theorem routeCut_ge_one {n : ℕ} (S : Finset (Fin n)) (r : List (Fin n))
    (hinter : (S ∩ r.toFinset).Nonempty) : 1 ≤ routeCut S r := by
  unfold routeCut
  rw [routeArcs_chain]
  apply chain_cut_ge_one (customerNodes S) 0 0 (r.map Fin.succ)
  · simp [customerNodes]
  · obtain ⟨j, hj⟩ := hinter
    have hjs := (Finset.mem_inter.mp hj).1
    have hjr := (Finset.mem_inter.mp hj).2
    exact ⟨j.succ, List.mem_map.mpr ⟨j, List.mem_toFinset.mp hjr, rfl⟩,
      Finset.mem_image.mpr ⟨j, hjs, rfl⟩⟩

theorem incomingCut_eq_routeCuts {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (S : Finset (Fin n)) :
    (∑ i ∈ (customerNodes S)ᶜ, ∑ j ∈ customerNodes S, inducedFlow R i j) =
      ∑ k, routeCut S (R k) := by
  have hw := flow_weight_sum_eq hR (fun i j => edgeCut (customerNodes S) (i, j))
  have hl : (∑ i, ∑ j, inducedFlow R i j • edgeCut (customerNodes S) (i, j)) =
      ∑ i ∈ (customerNodes S)ᶜ, ∑ j ∈ customerNodes S, inducedFlow R i j := by
    calc
      _ = ∑ i, if i ∈ (customerNodes S)ᶜ then
          ∑ j ∈ customerNodes S, inducedFlow R i j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ customerNodes S
        · simp [edgeCut, hi]
        · simp [edgeCut, hi, mul_ite]
      _ = _ := Finset.sum_ite_mem_eq _ _
  exact hl.symm.trans hw

theorem routeCut_self {n : ℕ} (r : List (Fin n)) (hr : r ≠ []) :
    routeCut r.toFinset r = 1 := by
  have hl : ∀ v ∈ r.map Fin.succ, v ∈ customerNodes r.toFinset := by
    rintro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact Finset.mem_image.mpr ⟨j, List.mem_toFinset.mpr hj, rfl⟩
  have ht : (0 : Fin (n + 1)) ∉ customerNodes r.toFinset := by simp [customerNodes]
  have hne : r.map Fin.succ ≠ [] := by simpa using hr
  have h := chain_cut_all (customerNodes r.toFinset) 0 0 (r.map Fin.succ) ht hl
  simpa [routeCut, routeArcs_chain, ht, hne] using h

theorem routeCut_other {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    {k l : Fin m} (hkl : l ≠ k) : routeCut (R k).toFinset (R l) = 0 := by
  have hl : ∀ v ∈ (R l).map Fin.succ, v ∉ customerNodes (R k).toFinset := by
    rintro v hv hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hm
    have hba : b = a := Fin.succ_injective n he
    subst b
    exact List.disjoint_left.mp (routeSet_disjoint hR hkl) ha (List.mem_toFinset.mp hb)
  have ht : (0 : Fin (n + 1)) ∉ customerNodes (R k).toFinset := by simp [customerNodes]
  simpa only [routeCut, routeArcs_chain] using
    chain_cut_none (customerNodes (R k).toFinset) 0 0 ((R l).map Fin.succ) ht hl

theorem whole_route_incoming_cut {n m : ℕ} {R : Fin m → List (Fin n)} (hR : IsRouteSet R)
    (k : Fin m) :
    (∑ i ∈ (customerNodes (R k).toFinset)ᶜ,
      ∑ j ∈ customerNodes (R k).toFinset, inducedFlow R i j) = 1 := by
  rw [incomingCut_eq_routeCuts hR]
  have he (l : Fin m) : routeCut (R k).toFinset (R l) = if l = k then 1 else 0 := by
    by_cases hl : l = k
    · subst l; simp [routeCut_self _ (hR.1 k)]
    · simp only [if_neg hl, routeCut_other hR hl]
  simp_rw [he]
  simp

end DRCVRP.RCI.Checked
end


/- Inlined checked module: RouteToFlow -/
section
open MeasureTheory

namespace DRCVRP.RCI.Checked

theorem route_intersections_union {n m : ℕ} {R : Fin m → List (Fin n)}
    (hR : IsRouteSet R) (S : Finset (Fin n)) :
    Finset.univ.biUnion (fun k => S ∩ (R k).toFinset) = S := by
  ext j
  constructor
  · intro hj
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_inter.mp hk).1
  · intro hj
    obtain ⟨k, hk⟩ := routeSet_covers hR j
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨hj, List.mem_toFinset.mpr hk⟩⟩

theorem inducedFlow_capacity {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (eps Q : ℝ)
    (he0 : 0 < eps) (he1 : eps < 1) (hQ : 0 < Q)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hsub : IsSubadditive Amb eps Q) {R : Fin m → List (Fin n)}
    (hR : RVRPFeasible Amb eps Q R) (S : Finset (Fin n)) :
    demandEstimator Amb eps Q S ≤
      ((∑ i ∈ (customerNodes S)ᶜ, ∑ j ∈ customerNodes S, inducedFlow R i j : ℕ) : ℤ) := by
  have hu := route_intersections_union hR.1 S
  have hs := estimator_biUnion_le_sum Amb eps Q hsub Finset.univ
    (fun k => S ∩ (R k).toFinset)
  rw [hu] at hs
  calc
    _ ≤ ∑ k, demandEstimator Amb eps Q (S ∩ (R k).toFinset) := hs
    _ ≤ ∑ k, (routeCut S (R k) : ℤ) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hne : (S ∩ (R k).toFinset).Nonempty
      · have hb := subset_route_estimator_le_one Amb hAmb eps Q he0 he1 hQ hnonneg
          (R k) (routeSet_nodup hR.1 k) (hR.2 k) (S ∩ (R k).toFinset)
          Finset.inter_subset_right
        have hc : (1 : ℤ) ≤ (routeCut S (R k) : ℤ) := by
          exact_mod_cast routeCut_ge_one S (R k) hne
        exact hb.trans hc
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hempty, demandEstimator_empty]
        exact Int.natCast_nonneg _
    _ = _ := by exact_mod_cast (incomingCut_eq_routeCuts hR.1 S).symm

theorem rvrp_to_flow_checked {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (Q : ℝ) (hQ : 0 < Q) (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hsub : IsSubadditive Amb eps Q) (R : Fin m → List (Fin n))
    (hR : RVRPFeasible Amb eps Q R) :
    TwoIndexFeasible Amb eps Q m (inducedFlow R) ∧
      flowCost c (inducedFlow R) = routeSetCost c R := by
  refine ⟨⟨?_, inducedFlow_diag hR.1, inducedFlow_out_degree hR.1,
    inducedFlow_in_degree hR.1, ?_⟩, routeSet_flow_cost hR.1 c⟩
  · intro i j
    unfold inducedFlow
    split_ifs <;> simp
  · intro S _
    exact inducedFlow_capacity Amb hAmb eps Q he0 he1 hQ hnonneg hsub hR S

end DRCVRP.RCI.Checked
end


/- Inlined checked module: PredecessorTermination -/
section
namespace DRCVRP.RCI.Decomposition

variable {V : Type*}

/-- A finite predecessor graph with an entering predecessor for every nonempty set avoiding
the depot reaches the depot from each vertex. This excludes customer-only cycles. -/
theorem predecessor_reaches_depot [Fintype V] (depot : V) (pred : V → V)
    (hcut : ∀ S : Finset V, S.Nonempty → depot ∉ S → ∃ v ∈ S, pred v ∉ S) :
    ∀ v : V, ∃ k : ℕ, pred^[k] v = depot := by
  classical
  intro v
  by_contra hv
  let S : Finset V := Finset.univ.filter (fun w => ¬ ∃ k : ℕ, pred^[k] w = depot)
  have hmem : ∀ w : V, w ∈ S ↔ ¬ ∃ k : ℕ, pred^[k] w = depot := by
    intro w
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : S.Nonempty := ⟨v, (hmem v).mpr hv⟩
  have hd : depot ∉ S := by
    rw [hmem]
    exact fun h => h ⟨0, rfl⟩
  obtain ⟨w, hw, hp⟩ := hcut S hne hd
  have hp' : ∃ k : ℕ, pred^[k] (pred w) = depot := by
    by_contra hn
    exact hp ((hmem (pred w)).mpr hn)
  obtain ⟨k, hk⟩ := hp'
  exact (hmem w).mp hw ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩

noncomputable def predecessorDepth (depot : V) (pred : V → V)
    (hreach : ∀ v : V, ∃ k : ℕ, pred^[k] v = depot) (v : V) : ℕ :=
  by classical exact Nat.find (hreach v)

theorem predecessorDepth_spec (depot : V) (pred : V → V)
    (hreach : ∀ v : V, ∃ k : ℕ, pred^[k] v = depot) (v : V) :
    pred^[predecessorDepth depot pred hreach v] v = depot := by
  classical
  exact Nat.find_spec (hreach v)

theorem predecessorDepth_depot (depot : V) (pred : V → V)
    (hreach : ∀ v : V, ∃ k : ℕ, pred^[k] v = depot) :
    predecessorDepth depot pred hreach depot = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (hreach depot) (show pred^[0] depot = depot from rfl)

theorem predecessorDepth_succ (depot : V) (pred : V → V)
    (hreach : ∀ v : V, ∃ k : ℕ, pred^[k] v = depot) {v : V} (hv : v ≠ depot) :
    predecessorDepth depot pred hreach v = predecessorDepth depot pred hreach (pred v) + 1 := by
  classical
  have hpos : 0 < predecessorDepth depot pred hreach v := by
    by_contra hn
    have hz : predecessorDepth depot pred hreach v = 0 := by omega
    have hs := predecessorDepth_spec depot pred hreach v
    rw [hz] at hs
    exact hv hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
  have hstep : pred^[k] (pred v) = depot := by
    have hs := predecessorDepth_spec depot pred hreach v
    rw [hk, Function.iterate_succ_apply] at hs
    exact hs
  have hle : predecessorDepth depot pred hreach (pred v) ≤ k := Nat.find_min' _ hstep
  have hback : pred^[predecessorDepth depot pred hreach (pred v) + 1] v = depot := by
    rw [Function.iterate_succ_apply]
    exact predecessorDepth_spec depot pred hreach (pred v)
  have hle' : predecessorDepth depot pred hreach v ≤ predecessorDepth depot pred hreach (pred v) + 1 :=
    Nat.find_min' _ hback
  omega

end DRCVRP.RCI.Decomposition
end


/- Inlined checked module: FiniteFlowCore -/
section
namespace DRCVRP.RCI.Decomposition

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_unique_one_of_sum_one (f : V → ℕ) (hf : ∑ v, f v = 1) :
    ∃! v, f v = 1 := by
  obtain ⟨v, _, hv⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ v, f v by omega)
  have hle : f v ≤ 1 := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans_eq hf
  have heq : f v = 1 := by omega
  refine ⟨v, heq, ?_⟩
  intro w hw
  by_contra hne
  have hs : f w + f v ≤ ∑ z, f z := by
    calc
      f w + f v = ∑ z ∈ ({w, v} : Finset V), f z := by simp [hne]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- The finite flow properties needed for route decomposition; positive customer cuts rule
out components disconnected from the depot. -/
structure DepotFlow (depot : V) (x : V → V → ℕ) : Prop where
  diagonal : ∀ v, x v v = 0
  incoming : ∀ v, v ≠ depot → ∑ u, x u v = 1
  outgoing : ∀ v, v ≠ depot → ∑ u, x v u = 1
  cut_positive : ∀ S : Finset V, S.Nonempty → depot ∉ S →
    0 < ∑ u ∈ Sᶜ, ∑ v ∈ S, x u v

namespace DepotFlow

variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

noncomputable def predecessor (v : V) : V :=
  if hv : v = depot then depot else Classical.choose (exists_unique_one_of_sum_one (fun u => x u v) (h.incoming v hv))

noncomputable def successor (v : V) : V :=
  if hv : v = depot then depot else Classical.choose (exists_unique_one_of_sum_one (x v) (h.outgoing v hv))

theorem predecessor_depot : h.predecessor depot = depot := by simp [predecessor]

theorem successor_depot : h.successor depot = depot := by simp [successor]

theorem predecessor_spec {v : V} (hv : v ≠ depot) : x (h.predecessor v) v = 1 := by
  rw [predecessor, dif_neg hv]
  exact (Classical.choose_spec (exists_unique_one_of_sum_one (fun u => x u v) (h.incoming v hv))).1

theorem successor_spec {v : V} (hv : v ≠ depot) : x v (h.successor v) = 1 := by
  rw [successor, dif_neg hv]
  exact (Classical.choose_spec (exists_unique_one_of_sum_one (x v) (h.outgoing v hv))).1

theorem predecessor_eq_of_arc {u v : V} (hv : v ≠ depot) (huv : x u v = 1) :
    h.predecessor v = u := by
  rw [predecessor, dif_neg hv]
  exact ((Classical.choose_spec (exists_unique_one_of_sum_one (fun u => x u v) (h.incoming v hv))).2 u huv).symm

theorem successor_eq_of_arc {u v : V} (hu : u ≠ depot) (huv : x u v = 1) :
    h.successor u = v := by
  rw [successor, dif_neg hu]
  exact ((Classical.choose_spec (exists_unique_one_of_sum_one (x u) (h.outgoing u hu))).2 v huv).symm

theorem predecessor_cut (S : Finset V) (hne : S.Nonempty) (hd : depot ∉ S) :
    ∃ v ∈ S, h.predecessor v ∉ S := by
  obtain ⟨u, hu, hp⟩ := Finset.sum_pos_iff.mp (h.cut_positive S hne hd)
  obtain ⟨v, hv, huv⟩ := Finset.sum_pos_iff.mp hp
  have hvd : v ≠ depot := fun he => hd (he ▸ hv)
  have hle : x u v ≤ 1 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)).trans_eq (h.incoming v hvd)
  have heq : x u v = 1 := by omega
  refine ⟨v, hv, ?_⟩
  rw [h.predecessor_eq_of_arc hvd heq]
  exact Finset.mem_compl.mp hu

theorem reaches_depot (v : V) : ∃ k : ℕ, h.predecessor^[k] v = depot :=
  predecessor_reaches_depot depot h.predecessor h.predecessor_cut v

noncomputable def depth (v : V) : ℕ := predecessorDepth depot h.predecessor h.reaches_depot v

theorem depth_depot : h.depth depot = 0 :=
  predecessorDepth_depot depot h.predecessor h.reaches_depot

theorem depth_predecessor {v : V} (hv : v ≠ depot) :
    h.depth v = h.depth (h.predecessor v) + 1 :=
  predecessorDepth_succ depot h.predecessor h.reaches_depot hv

theorem depth_arc {u v : V} (hv : v ≠ depot) (huv : x u v = 1) :
    h.depth v = h.depth u + 1 := by
  rw [h.depth_predecessor hv, h.predecessor_eq_of_arc hv huv]

theorem depth_successor {u : V} (hu : u ≠ depot) (hs : h.successor u ≠ depot) :
    h.depth (h.successor u) = h.depth u + 1 := h.depth_arc hs (h.successor_spec hu)

end DepotFlow
end DRCVRP.RCI.Decomposition
end


/- Inlined checked module: BackwardPaths -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

noncomputable def backChain (h : DepotFlow depot x) : ℕ → V → List V
  | 0, _ => []
  | k + 1, v => if v = depot then [] else backChain h k (h.predecessor v) ++ [v]

noncomputable def pathTo (v : V) : List V := h.backChain (h.depth v) v

theorem pathTo_depot : h.pathTo depot = [] := by
  simp only [pathTo, h.depth_depot, backChain]

theorem pathTo_snoc {v : V} (hv : v ≠ depot) :
    h.pathTo v = h.pathTo (h.predecessor v) ++ [v] := by
  unfold pathTo
  rw [h.depth_predecessor hv]
  simp only [backChain, if_neg hv]

theorem mem_pathTo_self {v : V} (hv : v ≠ depot) : v ∈ h.pathTo v := by
  rw [h.pathTo_snoc hv]
  simp only [List.mem_append, List.mem_singleton, or_true]

theorem pathTo_properties (v : V) :
    (∀ u ∈ h.pathTo v, u ≠ depot ∧ h.depth u ≤ h.depth v) ∧ (h.pathTo v).Nodup := by
  induction v using (measure h.depth).wf.induction with
  | h v ih =>
    by_cases hv : v = depot
    · subst v
      simp only [h.pathTo_depot, List.not_mem_nil, false_implies, implies_true, List.nodup_nil, and_self]
    · have hlt : h.depth (h.predecessor v) < h.depth v := by rw [h.depth_predecessor hv]; omega
      have hp := ih (h.predecessor v) hlt
      rw [h.pathTo_snoc hv]
      constructor
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact ⟨(hp.1 u hu).1, (hp.1 u hu).2.trans hlt.le⟩
        · have he : u = v := List.mem_singleton.mp hu
          subst u
          exact ⟨hv, le_rfl⟩
      · apply List.Nodup.append hp.2 (List.nodup_singleton v)
        intro u hu huv
        have he : u = v := List.mem_singleton.mp huv
        subst u
        have hh := (hp.1 v hu).2
        omega

theorem depot_not_mem_pathTo (v : V) : depot ∉ h.pathTo v := by
  intro hm
  exact ((h.pathTo_properties v).1 depot hm).1 rfl

theorem pathTo_nodup (v : V) : (h.pathTo v).Nodup := (h.pathTo_properties v).2

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: PathAncestry -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

theorem pathTo_prefix_of_mem {u v : V} (hu : u ∈ h.pathTo v) :
    h.pathTo u <+: h.pathTo v := by
  induction v using (measure h.depth).wf.induction with
  | h v ih =>
    by_cases hv : v = depot
    · subst v
      simp only [h.pathTo_depot, List.not_mem_nil] at hu
    · have hlt : h.depth (h.predecessor v) < h.depth v := by rw [h.depth_predecessor hv]; omega
      rw [h.pathTo_snoc hv] at hu ⊢
      rcases List.mem_append.mp hu with hu | hu
      · exact (ih (h.predecessor v) hlt hu).trans (List.prefix_append _ _)
      · have he : u = v := List.mem_singleton.mp hu
        subst u
        rw [← h.pathTo_snoc hv]

theorem predecessor_mem_pathTo {u v : V} (hu : u ∈ h.pathTo v)
    (hp : h.predecessor u ≠ depot) : h.predecessor u ∈ h.pathTo v := by
  have hud : u ≠ depot := ((h.pathTo_properties v).1 u hu).1
  apply (h.pathTo_prefix_of_mem hu).subset
  rw [h.pathTo_snoc hud]
  exact List.mem_append_left _ (h.mem_pathTo_self hp)

theorem successor_mem_pathTo {u v : V} (hu : u ∈ h.pathTo v) (hne : u ≠ v) :
    h.successor u ∈ h.pathTo v := by
  induction v using (measure h.depth).wf.induction with
  | h v ih =>
    by_cases hv : v = depot
    · subst v
      simp only [h.pathTo_depot, List.not_mem_nil] at hu
    · have hlt : h.depth (h.predecessor v) < h.depth v := by rw [h.depth_predecessor hv]; omega
      have hud : u ≠ depot := ((h.pathTo_properties v).1 u hu).1
      rw [h.pathTo_snoc hv] at hu ⊢
      rcases List.mem_append.mp hu with hu | hu
      · by_cases he : u = h.predecessor v
        · have ha : x u v = 1 := by rw [he]; exact h.predecessor_spec hv
          rw [h.successor_eq_of_arc hud ha]
          simp only [List.mem_append, List.mem_singleton, or_true]
        · exact List.mem_append_left _ (ih (h.predecessor v) hlt hu he)
      · exact (hne (List.mem_singleton.mp hu)).elim

theorem terminal_eq_of_mem {u v : V} (hu : u ∈ h.pathTo v)
    (hend : h.successor u = depot) : u = v := by
  by_contra hne
  have hs := h.successor_mem_pathTo hu hne
  rw [hend] at hs
  exact h.depot_not_mem_pathTo v hs

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: EndpointPartition -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

noncomputable def remaining (v : V) : ℕ := Finset.univ.sup h.depth - h.depth v

theorem remaining_successor_lt {v : V} (hv : v ≠ depot) (hs : h.successor v ≠ depot) :
    h.remaining (h.successor v) < h.remaining v := by
  have hle : h.depth (h.successor v) ≤ Finset.univ.sup h.depth :=
    Finset.le_sup (Finset.mem_univ _)
  have heq := h.depth_successor hv hs
  unfold remaining
  omega

theorem exists_terminal_path {v : V} (hv : v ≠ depot) :
    ∃ e : V, e ≠ depot ∧ h.successor e = depot ∧ v ∈ h.pathTo e := by
  induction v using (measure h.remaining).wf.induction with
  | h v ih =>
    by_cases hs : h.successor v = depot
    · exact ⟨v, hv, hs, h.mem_pathTo_self hv⟩
    · obtain ⟨e, hed, he, hm⟩ := ih (h.successor v) (h.remaining_successor_lt hv hs) hs
      have hp : h.predecessor (h.successor v) = v :=
        h.predecessor_eq_of_arc hs (h.successor_spec hv)
      have hpd : h.predecessor (h.successor v) ≠ depot := by simpa only [hp] using hv
      have hmem := h.predecessor_mem_pathTo hm hpd
      rw [hp] at hmem
      exact ⟨e, hed, he, hmem⟩

theorem terminal_path_unique {v e f : V} (he : h.successor e = depot)
    (hf : h.successor f = depot) (hv₁ : v ∈ h.pathTo e) (hv₂ : v ∈ h.pathTo f) : e = f := by
  induction v using (measure h.remaining).wf.induction generalizing e f with
  | h v ih =>
    by_cases hve : v = e
    · subst v
      exact h.terminal_eq_of_mem hv₂ he
    · have hvd : v ≠ depot := ((h.pathTo_properties e).1 v hv₁).1
      have hvf : v ≠ f := by
        intro hh
        have hs : h.successor v = depot := by simpa only [hh] using hf
        exact hve (h.terminal_eq_of_mem hv₁ hs)
      have hs₁ := h.successor_mem_pathTo hv₁ hve
      have hs₂ := h.successor_mem_pathTo hv₂ hvf
      have hsd : h.successor v ≠ depot := ((h.pathTo_properties e).1 _ hs₁).1
      exact ih (h.successor v) (h.remaining_successor_lt hvd hsd) he hf hs₁ hs₂

theorem terminal_paths_disjoint {e f : V} (he : h.successor e = depot)
    (hf : h.successor f = depot) (hne : e ≠ f) : List.Disjoint (h.pathTo e) (h.pathTo f) := by
  intro v hv₁ hv₂
  exact hne (h.terminal_path_unique he hf hv₁ hv₂)

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: TerminalIndex -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

theorem outgoing_indicator {u : V} (hu : u ≠ depot) (v : V) :
    x u v = if h.successor u = v then 1 else 0 := by
  have hle : x u v ≤ 1 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans_eq (h.outgoing u hu)
  by_cases hs : h.successor u = v
  · rw [if_pos hs]
    simpa only [hs] using h.successor_spec hu
  · rw [if_neg hs]
    have hn : x u v ≠ 1 := fun he => hs (h.successor_eq_of_arc hu he)
    omega

noncomputable def terminals : Finset V :=
  Finset.univ.filter (fun v => v ≠ depot ∧ h.successor v = depot)

theorem mem_terminals {v : V} : v ∈ h.terminals ↔ v ≠ depot ∧ h.successor v = depot := by
  simp only [terminals, Finset.mem_filter, Finset.mem_univ, true_and]

theorem terminals_card : h.terminals.card = ∑ v, x v depot := by
  rw [terminals, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = depot
  · subst v
    simp only [ne_eq, not_true_eq_false, false_and, if_false, h.diagonal]
  · rw [h.outgoing_indicator hv]
    by_cases hs : h.successor v = depot <;> simp_all

noncomputable def terminalEquiv (m : ℕ) (hm : ∑ v, x v depot = m) :
    Fin m ≃ {v : V // v ∈ h.terminals} :=
  (Fintype.equivFinOfCardEq (show Fintype.card {v : V // v ∈ h.terminals} = m by
    rw [Fintype.card_coe, h.terminals_card, hm])).symm

noncomputable def indexedPath (m : ℕ) (hm : ∑ v, x v depot = m) (k : Fin m) : List V :=
  h.pathTo (h.terminalEquiv m hm k).val

theorem indexedPath_nonempty (m : ℕ) (hm : ∑ v, x v depot = m) (k : Fin m) :
    h.indexedPath m hm k ≠ [] := by
  have he := h.mem_terminals.mp (h.terminalEquiv m hm k).property
  have hv := h.mem_pathTo_self he.1
  intro hn
  change _ ∈ h.indexedPath m hm k at hv
  rw [hn] at hv
  exact List.not_mem_nil hv

theorem indexedPath_nodup (m : ℕ) (hm : ∑ v, x v depot = m) (k : Fin m) :
    (h.indexedPath m hm k).Nodup := h.pathTo_nodup _

theorem indexedPath_disjoint (m : ℕ) (hm : ∑ v, x v depot = m) {k l : Fin m}
    (hkl : k ≠ l) : List.Disjoint (h.indexedPath m hm k) (h.indexedPath m hm l) := by
  have hk := h.mem_terminals.mp (h.terminalEquiv m hm k).property
  have hl := h.mem_terminals.mp (h.terminalEquiv m hm l).property
  apply h.terminal_paths_disjoint hk.2 hl.2
  intro he
  exact hkl ((h.terminalEquiv m hm).injective (Subtype.ext he))

theorem indexedPath_covers (m : ℕ) (hm : ∑ v, x v depot = m) {v : V} (hv : v ≠ depot) :
    ∃ k : Fin m, v ∈ h.indexedPath m hm k := by
  obtain ⟨e, hed, he, hv⟩ := h.exists_terminal_path hv
  let a : {v : V // v ∈ h.terminals} := ⟨e, h.mem_terminals.mpr ⟨hed, he⟩⟩
  refine ⟨(h.terminalEquiv m hm).symm a, ?_⟩
  simpa only [indexedPath, Equiv.apply_symm_apply] using hv

theorem indexedPath_avoids_depot (m : ℕ) (hm : ∑ v, x v depot = m) (k : Fin m) :
    depot ∉ h.indexedPath m hm k := h.depot_not_mem_pathTo _

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: CanonicalPathEdges -/
section
namespace DRCVRP.RCI.Decomposition

open Checked

theorem chainEdges_snoc {V : Type*} (terminal a b : V) (l : List V) :
    chainEdges terminal a (l ++ [b]) = chainEdges b a l ++ [(b, terminal)] := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append, chainEdges, ih]

namespace DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

theorem chainEdges_pathTo {v : V} (hv : v ≠ depot) (terminal : V) :
    chainEdges terminal depot (h.pathTo v) =
      (h.pathTo v).map (fun u => (h.predecessor u, u)) ++ [(v, terminal)] := by
  induction v using (measure h.depth).wf.induction generalizing terminal with
  | h v ih =>
    have hlt : h.depth (h.predecessor v) < h.depth v := by rw [h.depth_predecessor hv]; omega
    rw [h.pathTo_snoc hv, chainEdges_snoc, List.map_append, List.map_singleton]
    by_cases hp : h.predecessor v = depot
    · simp only [hp, h.pathTo_depot, chainEdges, List.map_nil, List.nil_append]
    · rw [ih (h.predecessor v) hlt hp v]

theorem pathTo_eq_of_chain (a terminal : V) (l : List V)
    (ht : terminal ≠ depot) (hl : ∀ v ∈ l, v ≠ depot)
    (hedges : ∀ e ∈ chainEdges terminal a l, x e.1 e.2 = 1) :
    h.pathTo terminal = h.pathTo a ++ l ++ [terminal] := by
  induction l generalizing a with
  | nil =>
    have he : x a terminal = 1 := hedges (a, terminal) (by simp only [chainEdges, List.mem_singleton])
    rw [h.pathTo_snoc ht, h.predecessor_eq_of_arc ht he]
    simp only [List.append_nil]
  | cons b l ih =>
    have hb : b ≠ depot := hl b (List.mem_cons_self)
    have hab : x a b = 1 := hedges (a, b) (List.mem_cons_self)
    have ht' := ih b (fun v hv => hl v (List.mem_cons_of_mem _ hv))
      (fun e he => hedges e (List.mem_cons_of_mem _ he))
    rw [ht', h.pathTo_snoc hb, h.predecessor_eq_of_arc hb hab]
    simp only [List.append_assoc, List.singleton_append]

theorem pathTo_edges_valid {v : V} (hv : v ≠ depot) (hend : h.successor v = depot) :
    ∀ e ∈ chainEdges depot depot (h.pathTo v), x e.1 e.2 = 1 := by
  intro e he
  rw [h.chainEdges_pathTo hv] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    exact h.predecessor_spec (((h.pathTo_properties v).1 u hu).1)
  · have hh : e = (v, depot) := List.mem_singleton.mp he
    subst e
    simpa only [hend] using h.successor_spec hv

theorem indexedPath_edges_valid (m : ℕ) (hm : ∑ v, x v depot = m) (k : Fin m) :
    ∀ e ∈ chainEdges depot depot (h.indexedPath m hm k), x e.1 e.2 = 1 := by
  have hk := h.mem_terminals.mp (h.terminalEquiv m hm k).property
  exact h.pathTo_edges_valid hk.1 hk.2

end DepotFlow
end DRCVRP.RCI.Decomposition
end


/- Inlined checked module: CanonicalFlowCore -/
section
open MeasureTheory

namespace DRCVRP.RCI.Decomposition

theorem sum_filter_ne_eq {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℕ) (a : V) (ha : f a = 0) :
    (∑ v ∈ Finset.univ.filter (fun v => v ≠ a), f v) = ∑ v, f v := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = a
  · simp only [hv, ne_eq, not_true_eq_false, if_false, ha]
  · simp only [ne_eq, hv, not_false_eq_true, if_true]

theorem twoIndex_depotFlow {n m : ℕ} {Amb : Set (Measure (Fin n → ℝ))} {ε Q : ℝ}
    {x : Fin (n + 1) → Fin (n + 1) → ℕ} (hx : TwoIndexFeasible Amb ε Q m x) :
    DepotFlow (0 : Fin (n + 1)) x := by
  rcases hx with ⟨_, hdiag, hout, hin, hcut⟩
  refine ⟨hdiag, ?_, ?_, ?_⟩
  · intro v hv
    rw [← sum_filter_ne_eq (fun u => x u v) v (hdiag v), hin]
    simp only [nodeDegree, if_neg hv]
  · intro v hv
    rw [← sum_filter_ne_eq (x v) v (hdiag v), hout]
    simp only [nodeDegree, if_neg hv]
  · intro S hne hd
    let C : Finset (Fin n) := Finset.univ.filter (fun i => i.succ ∈ S)
    have hnodes : customerNodes C = S := by
      apply Finset.ext
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [customerNodes, Finset.mem_image, Fin.succ_ne_zero, and_false, exists_false, hd]
      · simp only [customerNodes, Finset.mem_image, C, Finset.mem_filter, Finset.mem_univ,
          true_and, Fin.succ_inj, exists_eq_right]
    have hC : C.Nonempty := by
      have him : (C.image Fin.succ).Nonempty := by
        change (customerNodes C).Nonempty
        rw [hnodes]
        exact hne
      exact Finset.image_nonempty.mp him
    have hlow : (1 : ℤ) ≤ demandEstimator Amb ε Q C := by
      rw [demandEstimator, if_neg hC.ne_empty]
      exact le_max_right _ _
    have hbound := hcut C hC
    rw [hnodes] at hbound
    omega

theorem twoIndex_depot_incoming {n m : ℕ} {Amb : Set (Measure (Fin n → ℝ))} {ε Q : ℝ}
    {x : Fin (n + 1) → Fin (n + 1) → ℕ} (hx : TwoIndexFeasible Amb ε Q m x) :
    (∑ v, x v 0) = m := by
  rw [← sum_filter_ne_eq (fun v => x v 0) 0 (hx.2.1 0), hx.2.2.2.1]
  simp only [nodeDegree, if_true]

end DRCVRP.RCI.Decomposition
end


/- Inlined checked module: ConstructRoutes -/
section
namespace DRCVRP.RCI.Decomposition

def customerList {n : ℕ} : List (Fin (n + 1)) → List (Fin n)
  | [] => []
  | v :: l => if hv : v = 0 then customerList l else v.pred hv :: customerList l

theorem customerList_map_succ {n : ℕ} (l : List (Fin (n + 1))) (hl : 0 ∉ l) :
    (customerList l).map Fin.succ = l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have hv : v ≠ 0 := fun he => hl (List.mem_cons.mpr (Or.inl he.symm))
    have ht : (0 : Fin (n + 1)) ∉ l := fun hm => hl (List.mem_cons_of_mem _ hm)
    rw [customerList, dif_neg hv, List.map_cons, Fin.succ_pred, ih ht]

namespace DepotFlow

variable {n m : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ}
variable (h : DepotFlow (0 : Fin (n + 1)) x) (hm : ∑ v, x v 0 = m)

noncomputable def customerRoutes (k : Fin m) : List (Fin n) :=
  customerList (h.indexedPath m hm k)

theorem customerRoutes_map (k : Fin m) :
    (h.customerRoutes hm k).map Fin.succ = h.indexedPath m hm k :=
  customerList_map_succ _ (h.indexedPath_avoids_depot m hm k)

theorem customerRoutes_nonempty (k : Fin m) : h.customerRoutes hm k ≠ [] := by
  intro he
  have hh := h.customerRoutes_map hm k
  rw [he, List.map_nil] at hh
  exact h.indexedPath_nonempty m hm k hh.symm

theorem customerRoutes_nodup (k : Fin m) : (h.customerRoutes hm k).Nodup := by
  apply List.Nodup.of_map Fin.succ
  rw [h.customerRoutes_map hm]
  exact h.indexedPath_nodup m hm k

theorem customerRoutes_disjoint {k l : Fin m} (hkl : k ≠ l) :
    List.Disjoint (h.customerRoutes hm k) (h.customerRoutes hm l) := by
  intro j hjk hjl
  have hk : j.succ ∈ h.indexedPath m hm k := by
    rw [← h.customerRoutes_map hm]
    exact List.mem_map_of_mem hjk
  have hl : j.succ ∈ h.indexedPath m hm l := by
    rw [← h.customerRoutes_map hm]
    exact List.mem_map_of_mem hjl
  exact h.indexedPath_disjoint m hm hkl hk hl

theorem customerRoutes_covers (j : Fin n) : ∃ k : Fin m, j ∈ h.customerRoutes hm k := by
  obtain ⟨k, hk⟩ := h.indexedPath_covers m hm (Fin.succ_ne_zero j)
  rw [← h.customerRoutes_map hm] at hk
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hk
  have hij : i = j := Fin.succ_injective n he
  subst i
  exact ⟨k, hi⟩

theorem customerRoutes_isRouteSet : IsRouteSet (h.customerRoutes hm) := by
  refine ⟨h.customerRoutes_nonempty hm, ?_⟩
  have hn : (List.ofFn (h.customerRoutes hm)).flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact h.customerRoutes_nodup hm k
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      exact h.customerRoutes_disjoint hm (ne_of_lt hkl)
  apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
  intro j
  constructor
  · intro _
    exact List.mem_finRange j
  · intro _
    obtain ⟨k, hk⟩ := h.customerRoutes_covers hm j
    exact List.mem_flatten.mpr ⟨h.customerRoutes hm k, List.mem_ofFn.mpr ⟨k, rfl⟩, hk⟩

end DepotFlow
end DRCVRP.RCI.Decomposition
end


/- Inlined checked module: ReconstructPaths -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

open Checked

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

theorem closed_chain_is_path (l : List V) (hne : l ≠ [])
    (hvertices : ∀ v ∈ l, v ≠ depot)
    (hedges : ∀ a ∈ chainEdges depot depot l, x a.1 a.2 = 1) :
    ∃ e : V, e ≠ depot ∧ h.successor e = depot ∧ l = h.pathTo e := by
  let e := l.getLast hne
  have hsplit : l.dropLast ++ [e] = l := List.dropLast_append_getLast hne
  have hem : e ∈ l := hsplit ▸ List.mem_append_right _ (List.mem_singleton_self e)
  have he : e ≠ depot := hvertices e hem
  have hedge : chainEdges depot depot l = chainEdges e depot l.dropLast ++ [(e, depot)] := by
    calc
      _ = chainEdges depot depot (l.dropLast ++ [e]) := congrArg (chainEdges depot depot) hsplit.symm
      _ = _ := chainEdges_snoc _ _ _ _
  have hfinal : x e depot = 1 :=
    hedges (e, depot) (hedge.symm ▸ List.mem_append_right _ (List.mem_singleton_self _))
  have hp := h.pathTo_eq_of_chain depot e l.dropLast he
    (fun v hv => hvertices v (hsplit ▸ List.mem_append_left _ hv))
    (fun a ha => hedges a (hedge.symm ▸ List.mem_append_left _ ha))
  rw [h.pathTo_depot, List.nil_append, hsplit] at hp
  exact ⟨e, he, h.successor_eq_of_arc he hfinal, hp.symm⟩

theorem indexedPath_arc_iff (m : ℕ) (hm : ∑ v, x v depot = m) (u v : V) :
    x u v = 1 ↔ ∃ k : Fin m, (u, v) ∈ chainEdges depot depot (h.indexedPath m hm k) := by
  constructor
  · intro huv
    by_cases hv : v = depot
    · subst v
      have hu : u ≠ depot := by
        intro he
        subst u
        rw [h.diagonal] at huv
        omega
      have hs : h.successor u = depot := h.successor_eq_of_arc hu huv
      let a : {v : V // v ∈ h.terminals} := ⟨u, h.mem_terminals.mpr ⟨hu, hs⟩⟩
      refine ⟨(h.terminalEquiv m hm).symm a, ?_⟩
      simp only [indexedPath, Equiv.apply_symm_apply]
      rw [h.chainEdges_pathTo hu]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · obtain ⟨k, hk⟩ := h.indexedPath_covers m hm hv
      refine ⟨k, ?_⟩
      have he := h.mem_terminals.mp (h.terminalEquiv m hm k).property
      change (u, v) ∈ chainEdges depot depot (h.pathTo (h.terminalEquiv m hm k).val)
      rw [h.chainEdges_pathTo he.1]
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨v, hk, ?_⟩
      rw [h.predecessor_eq_of_arc hv huv]
  · rintro ⟨k, hk⟩
    exact h.indexedPath_edges_valid m hm k (u, v) hk

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: FlowReconstruction -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {depot : V} {x : V → V → ℕ} (h : DepotFlow depot x)

include h in
theorem arc_binary (u v : V) : x u v = 0 ∨ x u v = 1 := by
  by_cases hu : u = depot
  · by_cases hv : v = depot
    · subst u
      subst v
      exact Or.inl (h.diagonal depot)
    · have hle : x u v ≤ 1 :=
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)).trans_eq (h.incoming v hv)
      omega
  · have hle : x u v ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans_eq (h.outgoing u hu)
    omega

end DRCVRP.RCI.Decomposition.DepotFlow

namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {n m : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ}
variable (h : DepotFlow (0 : Fin (n + 1)) x) (hm : ∑ v, x v 0 = m)

theorem customerRoutes_arcs (k : Fin m) :
    routeArcs (h.customerRoutes hm k) = Checked.chainEdges (0 : Fin (n + 1)) 0 (h.indexedPath m hm k) := by
  rw [Checked.routeArcs_chain, h.customerRoutes_map hm]

theorem customerRoutes_inducedFlow : inducedFlow (h.customerRoutes hm) = x := by
  funext u v
  have he : (∃ k : Fin m, (u, v) ∈ routeArcs (h.customerRoutes hm k)) ↔ x u v = 1 := by
    simp only [h.customerRoutes_arcs hm]
    exact (h.indexedPath_arc_iff m hm u v).symm
  unfold inducedFlow
  by_cases hx : x u v = 1
  · rw [if_pos (he.mpr hx), hx]
  · have hz : x u v = 0 := (h.arc_binary u v).resolve_right hx
    rw [if_neg (fun hh => hx (he.mp hh)), hz]

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: RouteUniqueness -/
section
namespace DRCVRP.RCI.Decomposition.DepotFlow

variable {n m : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ}
variable (h : DepotFlow (0 : Fin (n + 1)) x) (hm : ∑ v, x v 0 = m)

theorem route_matches_customerRoutes {R' : Fin m → List (Fin n)} (hR' : IsRouteSet R')
    (hflow : inducedFlow R' = x) (k : Fin m) :
    ∃ l : Fin m, R' k = h.customerRoutes hm l := by
  have hne : (R' k).map Fin.succ ≠ [] := by
    intro he
    exact hR'.1 k (List.map_eq_nil_iff.mp he)
  have hvertices : ∀ v ∈ (R' k).map Fin.succ, v ≠ (0 : Fin (n + 1)) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact Fin.succ_ne_zero i
  have hedges : ∀ a ∈ Checked.chainEdges (0 : Fin (n + 1)) 0 ((R' k).map Fin.succ),
      x a.1 a.2 = 1 := by
    intro a ha
    have harc : a ∈ routeArcs (R' k) := by simpa only [Checked.routeArcs_chain] using ha
    have hi : inducedFlow R' a.1 a.2 = 1 := by
      unfold inducedFlow
      exact if_pos ⟨k, harc⟩
    simpa only [hflow] using hi
  obtain ⟨e, hed, he, hp⟩ := h.closed_chain_is_path ((R' k).map Fin.succ) hne hvertices hedges
  let a : {v : Fin (n + 1) // v ∈ h.terminals} := ⟨e, h.mem_terminals.mpr ⟨hed, he⟩⟩
  let l : Fin m := (h.terminalEquiv m hm).symm a
  refine ⟨l, ?_⟩
  apply List.map_injective_iff.mpr (Fin.succ_injective n)
  rw [h.customerRoutes_map hm]
  change (R' k).map Fin.succ = h.pathTo ((h.terminalEquiv m hm) ((h.terminalEquiv m hm).symm a)).val
  rw [Equiv.apply_symm_apply]
  exact hp

theorem customerRoutes_unique {R' : Fin m → List (Fin n)} (hR' : IsRouteSet R')
    (hflow : inducedFlow R' = x) :
    ∃ σ : Equiv.Perm (Fin m), R' = h.customerRoutes hm ∘ σ := by
  classical
  choose f hf using h.route_matches_customerRoutes hm hR' hflow
  have hinj : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have hr : R' k = R' l := (hf k).trans ((congrArg (h.customerRoutes hm) hkl).trans (hf l).symm)
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil (R' k) (hR'.1 k)
    have hjl : j ∈ R' l := hr ▸ hj
    exact Checked.routeSet_disjoint hR' hne hj hjl
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, ?_⟩
  funext k
  exact hf k

end DRCVRP.RCI.Decomposition.DepotFlow
end


/- Inlined checked module: VehicleRoot -/
section
open MeasureTheory

namespace DRCVRP.RCI

/-- Theorem 1, p. 722: if `q̃ ≥ 0` `ℙ`-a.s. for all `ℙ ∈ 𝒫` and `d_𝒫` satisfies the subadditivity
condition (S), then RVRP(𝒫) and 2VF(𝒫) are equivalent: (i) every RVRP(𝒫)-feasible route set
induces via (3) a 2VF(𝒫)-feasible `x` of the same cost; (ii) every 2VF(𝒫)-feasible `x` is
induced via (3) by an RVRP(𝒫)-feasible route set, unique up to reordering the routes, of the
same cost.
Standing hypotheses: costs `c(i,j) ≥ 0`, capacity `Q > 0`, `ε ∈ (0,1)`, every `ℙ ∈ 𝒫`
(`Amb`) a probability distribution with `q̃ ≥ 0` `ℙ`-a.s., the worst-case VaR of every customer
set finite (the paper's `d_𝒫` is real valued), and `d_𝒫` subadditive, condition (S). -/
theorem rvrp_equiv_twoIndexFlow {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (_hc : ∀ i j, 0 ≤ c i j)
    (Q : ℝ) (hQ : 0 < Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hbdd : ∀ S : Finset (Fin n), BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb))
    (hsub : IsSubadditive Amb ε Q) :
    (∀ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R →
      TwoIndexFeasible Amb ε Q m (inducedFlow R) ∧ flowCost c (inducedFlow R) = routeSetCost c R) ∧
    (∀ x : Fin (n + 1) → Fin (n + 1) → ℕ, TwoIndexFeasible Amb ε Q m x →
      ∃ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R ∧ inducedFlow R = x ∧
        (∀ R' : Fin m → List (Fin n), IsRouteSet R' → inducedFlow R' = x →
          ∃ σ : Equiv.Perm (Fin m), R' = R ∘ σ) ∧
        flowCost c x = routeSetCost c R) := by
  constructor
  · intro R hR
    exact Checked.rvrp_to_flow_checked c Q hQ ε hε0 hε1 Amb hAmb hnonneg hsub R hR
  · intro x hx
    let h := Decomposition.twoIndex_depotFlow hx
    let hm := Decomposition.twoIndex_depot_incoming hx
    let R := h.customerRoutes hm
    have hR : IsRouteSet R := h.customerRoutes_isRouteSet hm
    have hflow : inducedFlow R = x := h.customerRoutes_inducedFlow hm
    refine ⟨R, ⟨hR, ?_⟩, hflow, ?_, ?_⟩
    · intro k
      apply (Checked.route_chance_iff_estimator Amb hAmb ε Q hε0 hε1 hQ
        (R k) (Checked.routeSet_nodup hR k) (hR.1 k) (hbdd (R k).toFinset)).mpr
      have hne : (R k).toFinset.Nonempty := by simpa using hR.1 k
      have hcap := hx.2.2.2.2 (R k).toFinset hne
      have hcut : (∑ i ∈ (customerNodes (R k).toFinset)ᶜ,
          ∑ j ∈ customerNodes (R k).toFinset, x i j) = 1 := by
        rw [← hflow]
        exact Checked.whole_route_incoming_cut hR k
      simpa only [hcut, Int.natCast_one] using hcap
    · intro R' hR' hflow'
      exact h.customerRoutes_unique hm hR' hflow'
    · rw [← hflow]
      exact Checked.routeSet_flow_cost hR c

end DRCVRP.RCI
end


open MeasureTheory DRCVRP.RCI

theorem solution {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (Q : ℝ) (hQ : 0 < Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hbdd : ∀ S : Finset (Fin n), BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb))
    (hsub : IsSubadditive Amb ε Q) :
    (∀ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R →
      TwoIndexFeasible Amb ε Q m (inducedFlow R) ∧ flowCost c (inducedFlow R) = routeSetCost c R) ∧
    (∀ x : Fin (n + 1) → Fin (n + 1) → ℕ, TwoIndexFeasible Amb ε Q m x →
      ∃ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R ∧ inducedFlow R = x ∧
        (∀ R' : Fin m → List (Fin n), IsRouteSet R' → inducedFlow R' = x →
          ∃ σ : Equiv.Perm (Fin m), R' = R ∘ σ) ∧
        flowCost c x = routeSetCost c R) := DRCVRP.RCI.rvrp_equiv_twoIndexFlow (m := m) c hc Q hQ ε hε0 hε1 Amb hAmb hnonneg hbdd hsub
