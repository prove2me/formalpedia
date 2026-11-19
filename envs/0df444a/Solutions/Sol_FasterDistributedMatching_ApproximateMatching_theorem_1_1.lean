-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:46:01.712208+00:00
-- url     : https://prove2.me/submissions/eea2972f-5546-42b3-91ae-6d29570148e2

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_1
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_3
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_general_graph_constant_approximation
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_fmu_local_booster

-- Solutions/Sol_potential_change.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Potential
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_as_edges (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G x v = ∑ e ∈ G.edgeFinset, if v ∈ e then x e else 0 := by
  unfold load RandomOrderCRS.fracDegree
  rw [G.incidenceFinset_eq_filter]
  exact sum_filter ..

lemma load_sub (x y : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => y e-x e) v = load G y v-load G x v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [Finset.sum_sub_distrib]

def endpointSum (f : Fin N → ℝ) : Sym2 (Fin N) → ℝ :=
  Sym2.lift ⟨fun u v => f u+f v,by intro u v; exact add_comm _ _⟩

lemma endpointSum_apply (f : Fin N → ℝ) (u v : Fin N) : endpointSum f s(u,v) = f u+f v := rfl

lemma weighted_loads (d : Sym2 (Fin N) → ℝ) (f : Fin N → ℝ) :
    (∑ v, f v*load G d v) = ∑ e ∈ G.edgeFinset, endpointSum f e*d e := by
  simp_rw [load_as_edges,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨⟨u,w⟩,rfl⟩ := e.exists_rep
  have huw : u ≠ w := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
  have hi (v : Fin N) : f v*(if v ∈ s(u,w) then d s(u,w) else 0) =
      (if v = u then f u*d s(u,w) else 0)+(if v = w then f w*d s(u,w) else 0) := by
    simp only [Sym2.mem_iff]
    by_cases h1 : v = u <;> by_cases h2 : v = w <;> simp_all
  simp_rw [hi,sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointSum_apply]
  ring

def linearCoefficient (x : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  1-4*endpointSum (load G x) e

lemma linearCoefficient_apply (x : Sym2 (Fin N) → ℝ) (u v : Fin N) :
    linearCoefficient G x s(u,v) = 1-4*load G x u-4*load G x v := by
  unfold linearCoefficient
  rw [endpointSum_apply]
  ring

lemma potential_change (x y : Sym2 (Fin N) → ℝ) :
    potential G y-potential G x =
      (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e))-
        2*(∑ v, (load G y v-load G x v)^2) := by
  have hpen : penalty G y-penalty G x =
      4*(∑ v, load G x v*(load G y v-load G x v))+
        2*(∑ v, (load G y v-load G x v)^2) := by
    unfold penalty
    simp only [mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    ring
  have hcross := weighted_loads G (fun e => y e-x e) (load G x)
  simp_rw [load_sub] at hcross
  have hlinear : (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e)) =
      totalWeight G y-totalWeight G x-4*(∑ v, load G x v*(load G y v-load G x v)) := by
    rw [hcross]
    unfold linearCoefficient totalWeight
    simp only [sub_mul,one_mul,mul_assoc,sum_sub_distrib,←mul_sum]
  unfold potential
  linarith

end Potential
end MatchingRounding

-- Solutions/Sol_matching_cover.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma endpoint_exists (e : Sym2 (Fin N)) : ∃ v, v ∈ e := by
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  exact ⟨u,Sym2.mem_mk_left _ _⟩

lemma maximum_matching : ∃ M : Finset G.edgeSet, SemiStreamMWM.IsMatching G M ∧ M.card = optimum G := by
  have hempty : (∅ : Finset G.edgeSet) ∈ SemiStreamMWM.matchings G := by
    simp [SemiStreamMWM.matchings,SemiStreamMWM.IsMatching]
  obtain ⟨M,hM,hcard⟩ := exists_mem_eq_sup (SemiStreamMWM.matchings G) ⟨∅,hempty⟩ Finset.card
  exact ⟨M,(mem_filter.mp hM).2,hcard.symm⟩

lemma maximum_covers (M : Finset G.edgeSet) (hM : SemiStreamMWM.IsMatching G M) (hcard : M.card = optimum G)
    (e : G.edgeSet) : ∃ f ∈ M, ∃ v, v ∈ e.val ∧ v ∈ f.val := by
  by_contra hcover
  have hdisj : ∀ f ∈ M, ∀ v ∈ e.val, v ∉ f.val := by
    intro f hf v hve hvf
    exact hcover ⟨f,hf,v,hve,hvf⟩
  have heM : e ∉ M := by
    intro he
    obtain ⟨v,hv⟩ := endpoint_exists e.val
    exact hdisj e he v hv hv
  have hins : SemiStreamMWM.IsMatching G (insert e M) := by
    intro a ha b hb hab v hva
    rcases mem_insert.mp ha with hae|haM
    · subst a
      rcases mem_insert.mp hb with hbe|hbM
      · exact (hab hbe.symm).elim
      · exact hdisj b hbM v hva
    · rcases mem_insert.mp hb with hbe|hbM
      · subst b
        intro hve
        exact hdisj a haM v hve hva
      · exact hM a haM b hbM hab v hva
  have hle : (insert e M).card ≤ optimum G := by
    exact le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_univ _,hins⟩)
  rw [card_insert_of_notMem heM,hcard] at hle
  omega

lemma weight_vertex_cover (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin N)) (hcover : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e) :
    totalWeight G x ≤ ∑ v ∈ S, load G x v := by
  simp_rw [MatchingRounding.load_as_edges]
  rw [sum_comm]
  apply sum_le_sum
  intro e he
  obtain ⟨v,hv,hve⟩ := hcover e (G.mem_edgeFinset.mp he)
  calc
    x e = (if v ∈ e then x e else 0) := (if_pos hve).symm
    _ ≤ ∑ u ∈ S, if u ∈ e then x e else 0 :=
      single_le_sum (f:=fun u => if u ∈ e then x e else 0) (fun u _ => by split_ifs <;> simp_all) hv

lemma halfload_weight_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/2) : totalWeight G x ≤ (optimum G : ℝ) := by
  obtain ⟨M,hM,hcard⟩ := maximum_matching G
  let S : Finset (Fin N) := M.biUnion (fun e => e.val.toFinset)
  have hc : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨f,hf,v,hve,hvf⟩ := maximum_covers G M hM hcard ⟨e,he⟩
    exact ⟨v,mem_biUnion.mpr ⟨f,hf,Sym2.mem_toFinset.mpr hvf⟩,hve⟩
  have hs : S.card ≤ 2*M.card := by
    calc
      S.card ≤ ∑ e ∈ M, e.val.toFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, (2:ℕ) := sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega)
      _ = 2*M.card := by simp [mul_comm]
  have hscast : (S.card : ℝ) ≤ 2*(M.card : ℝ) := by exact_mod_cast hs
  have hw := weight_vertex_cover G x hx S hc
  have hl : (∑ v ∈ S, load G x v) ≤ (S.card : ℝ)/2 := by
    calc
      _ ≤ ∑ _ ∈ S, (1/2:ℝ) := sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [div_eq_mul_inv]
  rw [hcard] at hscast
  linarith

lemma sum_loads (x : Sym2 (Fin N) → ℝ) : (∑ v, load G x v) = 2*totalWeight G x := by
  have h := MatchingRounding.weighted_loads G x (fun _ => 1)
  simp only [one_mul] at h
  have he (e : Sym2 (Fin N)) : MatchingRounding.endpointSum (fun _ : Fin N => (1:ℝ)) e = 2 := by
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    change MatchingRounding.endpointSum (fun _ : Fin N => (1:ℝ)) s(u,v) = 2
    rw [MatchingRounding.endpointSum_apply]
    norm_num
  simp_rw [he] at h
  exact h.trans (mul_sum ..).symm

lemma halfload_penalty_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/2) : penalty G x ≤ 2*totalWeight G x := by
  rw [←sum_loads G x]
  unfold penalty
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  have hn : 0 ≤ load G x v := by
    unfold load RandomOrderCRS.fracDegree
    exact sum_nonneg (fun e _ => hx e)
  nlinarith [hload v]

end BipartiteRounding

-- Solutions/Sol_dyadic_rounding.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def quantum (i : ℕ) : ℝ := 1/(2:ℝ)^i

lemma quantum_pos (i : ℕ) : 0 < quantum i := by unfold quantum; positivity
lemma quantum_succ (i : ℕ) : quantum i = 2*quantum (i+1) := by unfold quantum; rw [pow_succ]; field_simp

lemma quantum_antitone : Antitone quantum := by
  apply antitone_nat_of_succ_le
  intro i
  have h := quantum_succ i
  linarith [quantum_pos (i+1)]

def dyadicIndex (K : ℕ) (r : ℝ) : ℕ :=
  if h : ∃ i, i ≤ K ∧ quantum i ≤ r then Nat.find h else 0

lemma dyadicIndex_spec (K : ℕ) (r : ℝ) (hr : quantum K ≤ r) (hupper : r ≤ 1) :
    dyadicIndex K r ≤ K ∧ quantum (dyadicIndex K r) ≤ r ∧ r ≤ 2*quantum (dyadicIndex K r) := by
  let h : ∃ i, i ≤ K ∧ quantum i ≤ r := ⟨K,le_rfl,hr⟩
  unfold dyadicIndex
  rw [dif_pos h]
  refine ⟨(Nat.find_spec h).1,(Nat.find_spec h).2,?_⟩
  cases hidx : Nat.find h with
  | zero => simpa only [quantum,pow_zero,div_one,mul_one] using (show r ≤ (2:ℝ) by linarith)
  | succ i =>
    have hbad : ¬(i ≤ K ∧ quantum i ≤ r) := Nat.find_min h (by omega)
    have hiK : i ≤ K := by have hk := (Nat.find_spec h).1; omega
    have hlt : r < quantum i := lt_of_not_ge (fun hh => hbad ⟨hiK,hh⟩)
    rw [←quantum_succ i]
    exact hlt.le

variable {N : ℕ} (G : SimpleGraph (Fin N))

def scaledDyadic (K : ℕ) (f : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  if e ∈ G.edgeSet then quantum (dyadicIndex K (f e)+3) else 0

lemma scaledDyadic_bounds (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (e : Sym2 (Fin N)) :
    f e/16 ≤ scaledDyadic G K f e ∧ scaledDyadic G K f e ≤ f e/8 := by
  by_cases he : e ∈ G.edgeSet
  · rw [scaledDyadic,if_pos he]
    have hh := dyadicIndex_spec K (f e) (hlower e he) (hf.1 e).2
    have hscale : quantum (dyadicIndex K (f e)+3) = quantum (dyadicIndex K (f e))/8 := by
      unfold quantum
      rw [pow_add]
      norm_num
      ring
    rw [hscale]
    constructor <;> linarith [hh.2.1,hh.2.2]
  · rw [scaledDyadic,if_neg he,hf.2.1 e he]
    norm_num

lemma scaledDyadic_nonnegative (K : ℕ) (f : Sym2 (Fin N) → ℝ) :
    NonnegativeAssignment G (scaledDyadic G K f) := by
  constructor
  · intro e
    unfold scaledDyadic
    split_ifs <;> linarith [quantum_pos (dyadicIndex K (f e)+3)]
  · intro e he
    exact if_neg he

lemma scaledDyadic_load (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (v : Fin N) :
    load G (scaledDyadic G K f) v ≤ 1/8 := by
  calc
    _ ≤ ∑ e ∈ G.incidenceFinset v, f e/8 := sum_le_sum (fun e _ => (scaledDyadic_bounds G K f hf hlower e).2)
    _ = load G f v/8 := by simp only [load,RandomOrderCRS.fracDegree,sum_div]
    _ ≤ 1/8 := by
      have hh := hf.2.2 v
      change load G f v ≤ 1 at hh
      linarith

lemma smallload_potential (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/8) : totalWeight G x/2 ≤ potential G x := by
  have hpen : penalty G x ≤ totalWeight G x/2 := by
    have hs := sum_loads G x
    have hsq : (∑ v, (load G x v)^2) ≤ (∑ v, load G x v)/8 := by
      rw [sum_div]
      apply sum_le_sum
      intro v _
      have hn : 0 ≤ load G x v := by
        unfold load RandomOrderCRS.fracDegree
        exact sum_nonneg (fun e _ => hx e)
      nlinarith [hload v]
    unfold penalty
    linarith
  unfold potential
  linarith

lemma scaledDyadic_potential (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (hweight : (optimum G : ℝ)/4 ≤ totalWeight G f) :
    (optimum G : ℝ)/128 ≤ potential G (scaledDyadic G K f) := by
  have hw : totalWeight G f/16 ≤ totalWeight G (scaledDyadic G K f) := by
    unfold totalWeight
    rw [sum_div]
    exact sum_le_sum (fun e _ => (scaledDyadic_bounds G K f hf hlower e).1)
  have hp := smallload_potential G (scaledDyadic G K f) (scaledDyadic_nonnegative G K f).1
    (scaledDyadic_load G K f hf hlower)
  linarith

end BipartiteRounding

-- Solutions/Sol_bipartite_parameters.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def initialExponent (D : ℕ) : ℕ := Nat.clog 2 (max 2 D)+1
def startExponent (D : ℕ) : ℕ := max 16 (initialExponent D+3)
def stageCount (D : ℕ) : ℕ := startExponent D-16
def blockLength (D : ℕ) : ℕ := ⌈256*Real.sqrt ((startExponent D:ℝ)+1)⌉₊

lemma start_large (D : ℕ) : 16 ≤ startExponent D := le_max_left _ _
lemma stages_identity (D : ℕ) : stageCount D+16 = startExponent D := by unfold stageCount; have h := start_large D; omega
lemma initial_le_start (D : ℕ) : initialExponent D+3 ≤ startExponent D := le_max_right _ _

lemma initial_quantum_bound (D : ℕ) : quantum (initialExponent D) ≤ 1/(2*(max 1 D:ℕ):ℝ) := by
  unfold quantum initialExponent
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_succ]
  have hh := Nat.le_pow_clog (by decide : 1 < 2) (max 2 D)
  have hmax : max 1 D ≤ max 2 D := max_le_max_right _ (by decide : 1 ≤ 2)
  have hp : (max 1 D:ℝ) ≤ (2:ℝ)^Nat.clog 2 (max 2 D) := by exact_mod_cast hmax.trans hh
  norm_cast
  linarith

lemma length_large (D : ℕ) : 2 ≤ blockLength D := by
  have hs : 1 ≤ Real.sqrt ((startExponent D:ℝ)+1) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
  have hc := Nat.le_ceil (256*Real.sqrt ((startExponent D:ℝ)+1))
  have hcast : (2:ℝ) ≤ (blockLength D:ℝ) := by unfold blockLength; linarith
  exact_mod_cast hcast

lemma length_square (D : ℕ) : 65536*(stageCount D:ℝ) ≤ (blockLength D:ℝ)^2 := by
  have hc := Nat.le_ceil (256*Real.sqrt ((startExponent D:ℝ)+1))
  change 256*Real.sqrt ((startExponent D:ℝ)+1) ≤ (blockLength D:ℝ) at hc
  have hsq := Real.sq_sqrt (show 0 ≤ (startExponent D:ℝ)+1 by positivity)
  have hs := Real.sqrt_nonneg ((startExponent D:ℝ)+1)
  have hn : (stageCount D:ℝ) ≤ (startExponent D:ℝ) := by exact_mod_cast (show stageCount D ≤ startExponent D by unfold stageCount; omega)
  nlinarith

lemma clog_real_bound (D : ℕ) : (Nat.clog 2 (max 2 D):ℝ) ≤ degreeLog D+1 := by
  rw [←Real.natCeil_logb_natCast]
  norm_num only [Nat.cast_ofNat]
  have hlog : 0 ≤ Real.logb 2 (max 2 D:ℕ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ max 2 D by omega))
  have hceil := Nat.ceil_lt_add_one hlog
  have hle : Real.logb 2 (max 2 D:ℕ) ≤ degreeLog D := by
    unfold degreeLog logTwo
    rw [Nat.cast_max,Nat.cast_ofNat]
    exact le_max_right _ _
  linarith

end BipartiteRounding

-- Solutions/Sol_block_mis.lean

open Classical Finset Polynomial
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace BlockColorProof

variable {F : Type} [Field F] [Fintype F]

def poly {d : ℕ} (a : Fin d → F) : F[X] :=
  ∑ i : Fin d, monomial i.val (a i)

lemma poly_coeff {d : ℕ} (a : Fin d → F) (i : Fin d) : (poly a).coeff i.val = a i := by
  simp [poly,Polynomial.coeff_monomial,Fin.val_inj]

lemma poly_injective (d : ℕ) : Function.Injective (@poly F _ d) := by
  intro a b h
  funext i
  have hh := congrArg (fun p : F[X] => p.coeff i.val) h
  simpa only [poly_coeff] using hh

lemma degree_poly {d : ℕ} (a : Fin d → F) : (poly a).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.le_of_lt i.isLt)

lemma collisions {d : ℕ} (a b : Fin d → F) (hab : a ≠ b) :
    (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)).card ≤ d := by
  have hp : poly a - poly b ≠ 0 := sub_ne_zero.mpr (fun h => hab (poly_injective d h))
  have hsub : (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)) ⊆
      (poly a-poly b).roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change (poly a-poly b).eval x = 0
    rw [Polynomial.eval_sub,sub_eq_zero]
    exact (mem_filter.mp hx).2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (degree_poly a) (degree_poly b)))))

lemma separating_point {d k D : ℕ} (enc : Fin k ↪ (Fin d → F))
    (hsize : D*d < Fintype.card F) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hself : c ∉ ns) :
    ∃ x : F, ∀ b ∈ ns, (poly (enc c)).eval x ≠ (poly (enc b)).eval x := by
  let bad := ns.biUnion fun b => univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x
  have hbad : bad.card ≤ D*d := by
    calc
      _ ≤ ∑ b ∈ ns, (univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x).card :=
        card_biUnion_le
      _ ≤ ∑ _ ∈ ns, d := by
        apply sum_le_sum
        intro b hb
        exact collisions (enc c) (enc b) (fun h => hself (enc.injective h ▸ hb))
      _ ≤ D*d := by simpa using Nat.mul_le_mul_right d hns
  have hproper : bad ≠ univ := by
    intro h
    rw [h,card_univ] at hbad
    omega
  have hex : ∃ x : F, x ∉ bad := by
    by_contra h
    apply hproper
    ext x
    simp only [mem_univ,iff_true]
    by_contra hx
    exact h ⟨x,hx⟩
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  intro b hb heq
  exact hx (mem_biUnion.mpr ⟨b,hb,mem_filter.mpr ⟨mem_univ x,heq⟩⟩)

def nextPalette (D k : ℕ) : ℕ := 4*(D*Nat.clog 2 k+1)^2

lemma separating_family (D k : ℕ) :
    ∃ S : Fin k → Finset (Fin (nextPalette D k)),
      ∀ (c : Fin k) (ns : Finset (Fin k)), ns.card ≤ D → c ∉ ns →
        ∃ i ∈ S c, ∀ b ∈ ns, i ∉ S b := by
  let d := Nat.clog 2 k
  obtain ⟨q,hprime,hq,hqu⟩ := Nat.exists_prime_lt_and_le_two_mul (D*d+1) (by omega)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ q := hprime.two_le
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin d → ZMod q) := by
    simp only [Fintype.card_fin,Fintype.card_fun,ZMod.card]
    exact (Nat.le_pow_clog (by decide) k).trans (Nat.pow_le_pow_left hq2 d)
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hcard2 : Fintype.card (ZMod q × ZMod q) ≤ nextPalette D k := by
    simp only [Fintype.card_prod,ZMod.card]
    unfold nextPalette
    change q*q ≤ 4*(D*d+1)^2
    nlinarith
  let E : (ZMod q × ZMod q) ↪ Fin (nextPalette D k) :=
    (Fintype.equivFin (ZMod q × ZMod q)).toEmbedding.trans (Fin.castLEEmb hcard2)
  let S : Fin k → Finset (Fin (nextPalette D k)) := fun c =>
    univ.image fun x : ZMod q => E (x,(poly (enc c)).eval x)
  refine ⟨S,?_⟩
  intro c ns hns hc
  have hsize : D*d < Fintype.card (ZMod q) := by simpa using (by omega : D*d < q)
  obtain ⟨x,hx⟩ := separating_point enc hsize c ns hns hc
  refine ⟨E (x,(poly (enc c)).eval x),mem_image.mpr ⟨x,mem_univ x,rfl⟩,?_⟩
  intro b hb hmem
  obtain ⟨y,_,hy⟩ := mem_image.mp hmem
  have heq := E.injective hy
  have hyx : y = x := congrArg Prod.fst heq
  have hev := congrArg Prod.snd heq
  apply hx b hb
  simpa only [hyx] using hev.symm

def family (D k : ℕ) : Fin k → Finset (Fin (nextPalette D k)) :=
  (separating_family D k).choose

lemma family_spec (D k : ℕ) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hc : c ∉ ns) :
    ∃ i ∈ family D k c, ∀ b ∈ ns, i ∉ family D k b :=
  (separating_family D k).choose_spec c ns hns hc

def finiteNeighbors (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) : Finset (Fin k) :=
  ns.attach.image fun b => ⟨b.val,hns b.val b.property⟩

lemma finiteNeighbors_card (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) :
    (finiteNeighbors k ns hns).card ≤ ns.card := by
  exact (card_image_le).trans_eq (card_attach)

lemma finiteNeighbors_mem (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) (b : Fin k) :
    b ∈ finiteNeighbors k ns hns ↔ b.val ∈ ns := by
  constructor
  · intro hb
    obtain ⟨c,hc,heq⟩ := mem_image.mp hb
    exact (congrArg Fin.val heq) ▸ c.property
  · intro hb
    exact mem_image.mpr ⟨⟨b.val,hb⟩,mem_attach _ _,Fin.ext rfl⟩

def localReduce (D k c : ℕ) (ns : Finset ℕ) : ℕ :=
  if h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k then
    let nsFin := finiteNeighbors k ns h.2.2.2
    let hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
      intro hm
      exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
    ((family_spec D k ⟨c,h.1⟩ nsFin
      ((finiteNeighbors_card k ns h.2.2.2).trans h.2.1) hc).choose).val
  else 0

lemma localReduce_spec (D k c : ℕ) (ns : Finset ℕ)
    (h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k) :
    ∃ i : Fin (nextPalette D k), localReduce D k c ns = i.val ∧
      i ∈ family D k ⟨c,h.1⟩ ∧ ∀ b (hb : b ∈ ns), i ∉ family D k ⟨b,h.2.2.2 b hb⟩ := by
  let nsFin := finiteNeighbors k ns h.2.2.2
  have hcard : nsFin.card ≤ D := (finiteNeighbors_card k ns h.2.2.2).trans h.2.1
  have hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
    intro hm
    exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
  have hex := family_spec D k ⟨c,h.1⟩ nsFin hcard hc
  refine ⟨hex.choose,?_,hex.choose_spec.1,?_⟩
  · unfold localReduce
    rw [dif_pos h]
  · intro b hb
    exact hex.choose_spec.2 _ ((finiteNeighbors_mem k ns h.2.2.2 _).mpr hb)

lemma localReduce_lt (D k c : ℕ) (ns : Finset ℕ) : localReduce D k c ns < nextPalette D k := by
  unfold localReduce
  split_ifs
  · exact Fin.isLt _
  · unfold nextPalette
    positivity

lemma localReduce_distinct (D k c b : ℕ) (ns ms : Finset ℕ)
    (hc : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ j ∈ ns, j < k)
    (hb : b < k ∧ ms.card ≤ D ∧ b ∉ ms ∧ ∀ j ∈ ms, j < k)
    (hbn : b ∈ ns) : localReduce D k c ns ≠ localReduce D k b ms := by
  obtain ⟨i,hi,hif,hin⟩ := localReduce_spec D k c ns hc
  obtain ⟨j,hj,hjf,hjn⟩ := localReduce_spec D k b ms hb
  intro heq
  have hij : i = j := Fin.ext (hi.symm.trans (heq.trans hj))
  exact hin b hbn (hij ▸ hjf)

lemma local_reduce_proper {V : Type} [Fintype V] (H : SimpleGraph V)
    (D k : ℕ) (col : V → ℕ) (hcol : Proper H k col)
    (hD : ∀ v, H.degree v ≤ D) :
    Proper H (nextPalette D k)
      (fun v => localReduce D k (col v) ((H.neighborFinset v).image col)) := by
  have hgood (v : V) : col v < k ∧ ((H.neighborFinset v).image col).card ≤ D ∧
      col v ∉ (H.neighborFinset v).image col ∧
      ∀ j ∈ (H.neighborFinset v).image col, j < k := by
    refine ⟨hcol.1 v,(card_image_le).trans ?_,?_,?_⟩
    · simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hD v
    · intro h
      obtain ⟨w,hw,heq⟩ := mem_image.mp h
      exact hcol.2 v w (by simpa using hw) heq.symm
    · intro j hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      exact hcol.1 w
  refine ⟨fun v => localReduce_lt D k _ _,?_⟩
  intro v w hvw
  exact localReduce_distinct D k (col v) (col w) _ _ (hgood v) (hgood w)
    (mem_image.mpr ⟨w,by simpa using hvw,rfl⟩)

lemma nextPalette_bound (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D k ≤ 16 * D^2 * (Nat.clog 2 k)^2 := by
  have hd : 1 ≤ Nat.clog 2 k := Nat.clog_pos (by decide) (by omega)
  unfold nextPalette
  have hm : 1 ≤ D * Nat.clog 2 k := by nlinarith
  nlinarith

lemma clog_nextPalette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    Nat.clog 2 (nextPalette D k) ≤ 4+2*Nat.clog 2 D+2*Nat.clog 2 (Nat.clog 2 k) := by
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ 16 * D^2 * (Nat.clog 2 k)^2 := nextPalette_bound D k hD hk
    _ ≤ 16 * (2^Nat.clog 2 D)^2 * (2^Nat.clog 2 (Nat.clog 2 k))^2 := by
      gcongr
      · exact Nat.le_pow_clog (by decide) _
      · exact Nat.le_pow_clog (by decide) _
    _ = _ := by
      simp only [pow_add,← pow_mul,Nat.mul_comm]
      norm_num

lemma polynomial_le_exponential (l : ℕ) (hl : 64 ≤ l) :
    (32*l)^4 ≤ 2^(l-1) := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    have hratio : (32*(l+1))^4 ≤ 2*(32*l)^4 := by
      have hsmall : 8*(l+1) ≤ 9*l := by omega
      have hp := Nat.pow_le_pow_left hsmall 4
      simp only [mul_pow] at hp
      norm_num at hp
      have hp' : 4096*(l+1)^4 ≤ 8192*l^4 := hp.trans
        (Nat.mul_le_mul_right _ (by decide : 6561 ≤ 8192))
      have hh : (l+1)^4 ≤ 2*l^4 := by omega
      calc
        _ = 32^4 * (l+1)^4 := by ring
        _ ≤ 32^4 * (2*l^4) := Nat.mul_le_mul_left _ hh
        _ = _ := by ring
    calc
      _ ≤ 2*(32*l)^4 := hratio
      _ ≤ 2*2^(l-1) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [show l+1-1 = (l-1)+1 by omega,pow_succ]; omega

lemma clog_fourth_bound (d : ℕ) (hd : 2^64 ≤ d) :
    (32*Nat.clog 2 d)^4 ≤ d := by
  have hlog : 64 ≤ Nat.clog 2 d := by
    have ht : 2^63 < d := by omega
    have hh := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr ht
    omega
  have hp := polynomial_le_exponential (Nat.clog 2 d) hlog
  have hd1 : 1 < d := by omega
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hd1
  exact hp.trans (by simpa only [Nat.pred_eq_sub_one] using hpred.le)

lemma two_step_palette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D (nextPalette D k) ≤ max (D^64) (Nat.clog 2 k) := by
  let d := Nat.clog 2 k
  let a := Nat.clog 2 D
  let b := Nat.clog 2 d
  have ha : a ≤ D := Nat.clog_le_of_le_pow (show D ≤ 2^D from (Nat.lt_pow_self (by decide : 1 < 2)).le)
  have hd : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  have hlog : Nat.clog 2 (nextPalette D k) ≤ 4+2*a+2*b := clog_nextPalette D k hD hk
  have hnext : nextPalette D (nextPalette D k) ≤ 4*(D*(4+2*a+2*b)+1)^2 := by
    unfold nextPalette
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.mul_le_mul_left D hlog) 1) 2)
  by_cases hsmall : d ≤ D^64
  · have hb : b ≤ 64*a := by
      apply Nat.clog_le_of_le_pow
      calc
        d ≤ D^64 := hsmall
        _ ≤ (2^a)^64 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) D) 64
        _ = _ := by rw [← pow_mul,Nat.mul_comm]
    have hinner : D*(4+2*a+2*b)+1 ≤ 135*D^2 := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 72900*D^4 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(135*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hconst : 72900 ≤ D^60 :=
      (by norm_num : 72900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
    apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ 72900*D^4 := hbound
      _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
      _ = _ := by rw [← pow_add]
  · have hlarge : 2^64 ≤ d := (Nat.pow_le_pow_left hD 64).trans (by omega)
    have hfour : (32*b)^4 ≤ d := clog_fourth_bound d hlarge
    have hD4 : D^4 ≤ d :=
      (Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 4 ≤ 64)).trans (by omega)
    have hDpow : D ≤ D^4 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 1 ≤ 4)
    have hDle : D ≤ d := hDpow.trans hD4
    have hab : a ≤ b := Nat.clog_mono_right 2 hDle
    have hb : 1 ≤ b := Nat.clog_pos (by decide) (by omega)
    have hinner : D*(4+2*a+2*b)+1 ≤ 16*D*b := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 1024*D^2*b^2 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(16*D*b)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hsquare : (1024*D^2*b^2)^2 ≤ d^2 := by
      calc
        _ = D^4*(32*b)^4 := by ring
        _ ≤ D^4*d := Nat.mul_le_mul_left _ hfour
        _ ≤ d*d := Nat.mul_le_mul_right d hD4
        _ = _ := by ring
    have hlast : 1024*D^2*b^2 ≤ d := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare
    exact (hbound.trans hlast).trans (le_max_right _ _)

lemma nextPalette_mono (D : ℕ) : Monotone (nextPalette D) := by
  intro a b hab
  unfold nextPalette
  gcongr

lemma nextPalette_threshold (D : ℕ) (hD : 2 ≤ D) : nextPalette D (D^64) ≤ D^64 := by
  have hclog : Nat.clog 2 (D^64) ≤ 64*D := by
    apply Nat.clog_le_of_le_pow
    calc
      D^64 ≤ (2^D)^64 := Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < 2)).le 64
      _ = _ := by rw [← pow_mul,Nat.mul_comm]
  have hinner : D*Nat.clog 2 (D^64)+1 ≤ 65*D^2 := by nlinarith
  have hconst : 16900 ≤ D^60 :=
    (by norm_num : 16900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
  calc
    _ = 4*(D*Nat.clog 2 (D^64)+1)^2 := rfl
    _ ≤ 4*(65*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
    _ = 16900*D^4 := by ring
    _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
    _ = _ := by rw [← pow_add]

def paddedNext (D k : ℕ) : ℕ := max (D^64) (nextPalette D k)

lemma paddedNext_mono (D : ℕ) : Monotone (paddedNext D) :=
  fun _ _ h => max_le_max_left _ (nextPalette_mono D h)

lemma paddedNext_twice (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    paddedNext D (paddedNext D k) ≤ max (D^64) (Nat.clog 2 k) := by
  unfold paddedNext
  apply max_le (le_max_left _ _)
  by_cases h : nextPalette D k ≤ D^64
  · rw [max_eq_left h]
    exact (nextPalette_threshold D hD).trans (le_max_left _ _)
  · rw [max_eq_right (by omega : D^64 ≤ nextPalette D k)]
    exact two_step_palette D k hD hk

lemma clog_lt_self (n : ℕ) (hn : 2 ≤ n) : Nat.clog 2 n < n := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_ |>.trans_lt (Nat.pred_lt (by omega))
  have hpow : n ≤ 2^(n-1) := by
    induction n,hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [show n+1-1 = (n-1)+1 by omega,pow_succ]
      omega
  simpa only [Nat.pred_eq_sub_one] using hpow

def height (n : ℕ) : ℕ := if h : n ≤ 1 then 0 else 1+height (Nat.clog 2 n)
termination_by n
 decreasing_by exact clog_lt_self n (by omega)

lemma height_le_self (n : ℕ) : height n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [height]
    split_ifs with hn
    · omega
    · have hlt := clog_lt_self n (by omega)
      have hh := ih _ hlt
      omega

lemma height_mono : Monotone height := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases ha : a ≤ 1
    · rw [height,dif_pos ha]; exact Nat.zero_le _
    · have hb : ¬ b ≤ 1 := by omega
      have hea : height a = 1+height (Nat.clog 2 a) := by rw [height,dif_neg ha]
      have heb : height b = 1+height (Nat.clog 2 b) := by rw [height,dif_neg hb]
      rw [hea,heb]
      have hlt := clog_lt_self b (by omega)
      exact Nat.add_le_add_left (ih _ hlt (Nat.clog_mono_right 2 hab)) 1

lemma height_pow_two (n : ℕ) (hn : 1 ≤ n) : height (2^n) = 1+height n := by
  rw [height,dif_neg (by
    have h : 2 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega),Nat.clog_pow 2 n (by decide)]

lemma square_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n^2 ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have hh : (n+1)^2 ≤ 2*n^2 := by nlinarith
    exact hh.trans (Nat.mul_le_mul_left 2 ih |>.trans_eq (by ring))

def tower (n : ℕ) : ℕ → ℕ
  | 0 => n
  | t+1 => 2^(tower n t)

lemma tower_ge (n t : ℕ) : n ≤ tower n t := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih.trans (Nat.lt_pow_self (by decide : 1 < 2)).le

lemma height_tower (n t : ℕ) (hn : 1 ≤ n) : height (tower n t) = t+height n := by
  induction t with
  | zero => simp [tower]
  | succ t ih =>
    rw [tower,height_pow_two _ (hn.trans (tower_ge n t)),ih]
    omega

lemma power_le_tower (n B : ℕ) (hn : 2 ≤ n) : n^B ≤ tower n B := by
  induction B with
  | zero => simpa [tower] using (show 1 ≤ n by omega)
  | succ B ih =>
    cases B with
    | zero => simpa [tower] using (Nat.lt_pow_self (by decide : 1 < 2) : n < 2^n).le
    | succ B =>
      have ht : 4 ≤ tower n (B+1) := by
        change 4 ≤ 2^(tower n B)
        exact (by norm_num : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (hn.trans (tower_ge n B)))
      calc
        n^(B+1+1) = n^(B+1)*n := by rw [pow_succ]
        _ ≤ (tower n (B+1))^2 := by
          simpa only [pow_two] using Nat.mul_le_mul ih (tower_ge n (B+1))
        _ ≤ 2^(tower n (B+1)) := square_le_two_pow _ ht
        _ = _ := rfl

lemma height_power (n B : ℕ) (hn : 2 ≤ n) : height (n^B) ≤ height n+B := by
  have h := height_mono (power_le_tower n B hn)
  rw [height_tower n B (by omega)] at h
  omega

lemma clog_ceil_log (x : ℝ) (hx : 0 < x) :
    Nat.clog 2 ⌈x⌉₊ = ⌈logTwo x⌉₊ := by
  apply eq_of_forall_ge_iff
  intro j
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2),Nat.ceil_le,Nat.ceil_le]
  rw [Nat.cast_pow,Nat.cast_ofNat]
  have h : logTwo x ≤ (j : ℝ) ↔ x ≤ (2 : ℝ)^(j : ℝ) :=
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx
  simpa only [Real.rpow_natCast] using h.symm

lemma iterLog_height (fuel : ℕ) (x : ℝ) (hx : 0 < x) (hf : ⌈x⌉₊ ≤ fuel) :
    iterLog fuel x = height ⌈x⌉₊ := by
  induction fuel generalizing x with
  | zero =>
    have hh : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    omega
  | succ fuel ih =>
    by_cases hx1 : x ≤ 1
    · have hn : ⌈x⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hx1)
      rw [iterLog,if_pos hx1,height,dif_pos hn]
    · have hn : ¬ ⌈x⌉₊ ≤ 1 := by
        intro h
        have hh := Nat.ceil_le.mp h
        norm_num at hh
        exact hx1 hh
      have hlog : 0 < logTwo x := Real.logb_pos (by norm_num) (by linarith)
      have hceil := clog_ceil_log x hx
      have hlt := clog_lt_self ⌈x⌉₊ (by omega)
      have hnext : ⌈logTwo x⌉₊ ≤ fuel := by omega
      rw [iterLog,if_neg hx1,ih _ hlog hnext]
      conv_rhs => rw [height,dif_neg hn]
      rw [← hceil]

lemma height_nat_iterLog (n : ℕ) : height n = iterLog n n := by
  by_cases hn : n = 0
  · subst n
    rw [height,dif_pos (by decide)]
    rfl
  · have h := iterLog_height n (n : ℝ) (by exact_mod_cast Nat.pos_of_ne_zero hn) (by simp)
    simpa using h.symm

lemma height_max (a b : ℕ) : height (max a b) = max (height a) (height b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (height_mono h)]
  · rw [max_eq_left h,max_eq_left (height_mono h)]

lemma height_two : height 2 = 1 := by
  rw [height,dif_neg (by decide)]
  change 1+height 1 = 1
  rw [height,dif_pos (by decide)]

lemma height_max_two (n : ℕ) : height (max 2 n) = logStar n := by
  rw [height_max,height_two,height_nat_iterLog]
  rfl

lemma height_ID_bound (n B : ℕ) : height ((max 2 n)^B) ≤ (B+1)*logStar n := by
  have hh := height_power (max 2 n) B (le_max_left _ _)
  rw [height_max_two] at hh
  have hpos : 1 ≤ logStar n := le_max_left _ _
  nlinarith

lemma palette_iterations (D k : ℕ) (hD : 2 ≤ D) :
    (paddedNext D)^[2*height k] (max (D^64) k) ≤ D^64 := by
  have hfix : paddedNext D (D^64) = D^64 := by
    exact max_eq_left (nextPalette_threshold D hD)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ D^64
    · rw [max_eq_left hk,Function.iterate_fixed hfix]
    · have hk2 : 2 ≤ k := by
        have hsmall : 2 ≤ D^64 := by
          exact (by norm_num : 2 ≤ 2^64).trans (Nat.pow_le_pow_left hD 64)
        omega
      have hh : height k = 1+height (Nat.clog 2 k) := by
        rw [height,dif_neg (by omega)]
      rw [hh,show 2*(1+height (Nat.clog 2 k)) = 2*height (Nat.clog 2 k)+2 by omega,
        Function.iterate_add_apply,max_eq_right (by omega : D^64 ≤ k)]
      have htwo : (paddedNext D)^[2] k ≤ max (D^64) (Nat.clog 2 k) := paddedNext_twice D k hD hk2
      apply le_trans ((paddedNext_mono D).iterate (2*height (Nat.clog 2 k)) htwo)
      exact ih _ (clog_lt_self k hk2)

structure ColorParameters where
  degree : ℕ
  palette : ℕ

structure ColorState where
  degree : ℕ
  palette : ℕ
  color : ℕ

def colorProgram : Deterministic ColorParameters ℕ ℕ where
  program := {
    State := ColorState
    Msg := ℕ
    rounds := fun k => 2*height k.palette
    init := fun k _ col _ => ⟨k.degree,max (k.degree^64) k.palette,col⟩
    send := ColorState.color
    step := fun s msgs => ⟨s.degree,paddedNext s.degree s.palette,
      localReduce s.degree s.palette s.color msgs.toFinset⟩
    out := ColorState.color }
  tape_independent := by intros; rfl

lemma colorProgram_invariant {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD : ∀ v, H.degree v ≤ k.degree) (t : ℕ) :
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    (∀ v, (run t v).degree = k.degree ∧
      (run t v).palette = (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)) ∧
    Proper H ((paddedNext k.degree)^[t] (max (k.degree^64) k.palette))
      (fun v => (run t v).color) := by
  dsimp only
  induction t with
  | zero =>
    refine ⟨fun v => ⟨rfl,rfl⟩,fun v => (hinit.1 v).trans_le (le_max_right _ _),?_⟩
    intro v w hvw heq
    exact hinit.2 v w hvw heq
  | succ t ih =>
    obtain ⟨hstate,hproper⟩ := ih
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    let Q := (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)
    have hnew := local_reduce_proper H k.degree _ _ hproper hD
    have hstep (v : V) : (run (t+1) v).color =
        localReduce k.degree Q (run t v).color
          ((H.neighborFinset v).image (fun w => (run t w).color)) := by
      change localReduce (run t v).degree (run t v).palette (run t v).color
        (((univ.filter (H.Adj v)).val.map fun w => (run t w).color).toFinset) = _
      rw [(hstate v).1,(hstate v).2]
      rw [← Finset.image_toFinset,Finset.val_toFinset,← H.neighborFinset_eq_filter]
    constructor
    · intro v
      constructor
      · change (run t v).degree = k.degree
        exact (hstate v).1
      · change paddedNext (run t v).degree (run t v).palette = _
        rw [(hstate v).1,(hstate v).2,Function.iterate_succ_apply']
    · simp only [Function.iterate_succ_apply']
      constructor
      · intro v
        change (run (t+1) v).color < paddedNext k.degree Q
        rw [hstep]
        exact (hnew.1 v).trans_le (le_max_right _ _)
      · intro v w hvw
        change (run (t+1) v).color ≠ (run (t+1) w).color
        rw [hstep,hstep]
        exact hnew.2 v w hvw

lemma colorProgram_correct {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    Proper H (k.degree^64)
      (colorProgram.program.output H k ids initial (fun _ _ => false)) := by
  have h := colorProgram_invariant H k ids initial hinit hD (2*height k.palette)
  have hp := palette_iterations k.degree k.palette hD2
  exact ⟨fun v => (h.2.1 v).trans_le hp,h.2.2⟩

lemma colorProgram_rounds (D n B : ℕ) :
    colorProgram.program.rounds ⟨D,(max 2 n)^B⟩ ≤ 2*(B+1)*logStar n := by
  change 2*height ((max 2 n)^B) ≤ _
  have h := Nat.mul_le_mul_left 2 (height_ID_bound n B)
  simpa only [mul_assoc] using h


def greedy {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) : ℕ → Finset V
  | 0 => ∅
  | t+1 => greedy H col t ∪ univ.filter (fun v => col v = t ∧
      ∀ w, H.Adj v w → w ∉ greedy H col t)

lemma greedy_step {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) (v : V) :
    v ∈ greedy H col (t+1) ↔ v ∈ greedy H col t ∨
      (col v = t ∧ ∀ w, H.Adj v w → w ∉ greedy H col t) := by
  simp only [greedy,mem_union,mem_filter,mem_univ,true_and]

lemma greedy_mono {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) :
    Monotone (greedy H col) := by
  apply monotone_nat_of_le_succ
  intro t v hv
  exact (greedy_step H col t v).mpr (Or.inl hv)

lemma greedy_independent {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (hc : ∀ v w, H.Adj v w → col v ≠ col w) (t : ℕ) :
    ∀ v ∈ greedy H col t, ∀ w ∈ greedy H col t, ¬ H.Adj v w := by
  induction t with
  | zero => simp [greedy]
  | succ t ih =>
    intro v hv w hw hvw
    rcases (greedy_step H col t v).mp hv with hold | hnew
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact ih v hold w holdw hvw
      · exact hneww.2 v hvw.symm hold
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact hnew.2 w hvw holdw
      · exact hc v w hvw (hnew.1.trans hneww.1.symm)

lemma greedy_dominates {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) :
    ∀ v, col v < t → v ∈ greedy H col t ∨ ∃ w, H.Adj v w ∧ w ∈ greedy H col t := by
  induction t with
  | zero => intro v hv; omega
  | succ t ih =>
    intro v hv
    by_cases hlt : col v < t
    · rcases ih v hlt with h | ⟨w,hw,hmem⟩
      · exact Or.inl (greedy_mono H col (Nat.le_succ t) h)
      · exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩
    · have heq : col v = t := by omega
      by_cases hn : ∀ w, H.Adj v w → w ∉ greedy H col t
      · exact Or.inl ((greedy_step H col t v).mpr (Or.inr ⟨heq,hn⟩))
      · push Not at hn
        obtain ⟨w,hw,hmem⟩ := hn
        exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩

structure MISState where
  colors : ColorState
  remaining : ℕ
  index : ℕ
  selected : Bool

def misProgram : Deterministic ColorParameters ℕ Bool where
  program := {
    State := MISState
    Msg := ℕ ⊕ Bool
    rounds := fun k => 2*height k.palette+k.degree^64
    init := fun k id initial _ =>
      ⟨colorProgram.program.init k id initial (fun _ => false),2*height k.palette,0,false⟩
    send := fun s => if 0 < s.remaining then Sum.inl s.colors.color else Sum.inr s.selected
    step := fun s msgs => if 0 < s.remaining then
      {s with remaining := s.remaining-1, colors := (colorProgram.program.step s.colors
        (msgs.filterMap fun m => match m with | .inl n => some n | .inr _ => none))}
      else {s with index := s.index+1, selected := (s.selected ||
        (decide (s.colors.color = s.index) && !decide (Sum.inr true ∈ msgs)))}
    out := MISState.selected }
  tape_independent := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
lemma mis_prefix {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (t : ℕ) (ht : t ≤ 2*height k.palette) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) t v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) t v,
        2*height k.palette-t,0,false⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    have hpos : 0 < 2*height k.palette-t := by omega
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih (by omega)]
    simp only [misProgram]
    simp only [hpos,if_true,Multiset.filterMap_map,Function.comp_def]
    change (⟨colorProgram.program.step
      (colorProgram.program.run H k ids initial (fun _ _ => false) t v)
        (Multiset.filterMap (some ∘ (fun w => (colorProgram.program.run H k ids initial (fun _ _ => false) t w).color))
          (univ.filter (H.Adj v)).val),2*height k.palette-t-1,0,false⟩ : MISState) = _
    rw [Multiset.filterMap_eq_map]
    congr 1

lemma greedy_bool_update {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (i : ℕ) (v : V) :
    (decide (v ∈ greedy H col i) || (decide (col v = i) &&
      !decide (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
        (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))))) =
      decide (v ∈ greedy H col (i+1)) := by
  have hm : (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
      (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))) ↔
        ∃ w, H.Adj v w ∧ w ∈ greedy H col i := by simp
  have hn : (∀ w, H.Adj v w → w ∉ greedy H col i) ↔
      ¬∃ w, H.Adj v w ∧ w ∈ greedy H col i := by aesop
  simp only [greedy_step,hn,hm]
  by_cases h₁ : v ∈ greedy H col i <;> by_cases h₂ : col v = i <;>
    by_cases h₃ : ∃ w, H.Adj v w ∧ w ∈ greedy H col i <;> simp [h₁,h₂,h₃]

lemma mis_greedy {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (i : ℕ) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette+i) v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette) v,
        0,i,decide (v ∈ greedy H
          (colorProgram.program.output H k ids initial (fun _ _ => false)) i)⟩ := by
  induction i with
  | zero =>
    intro v
    simpa only [Nat.add_zero,Nat.sub_self,greedy,notMem_empty,decide_false] using
      mis_prefix H k ids initial (2*height k.palette) le_rfl v
  | succ i ih =>
    intro v
    rw [show 2*height k.palette+(i+1) = (2*height k.palette+i)+1 by omega,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    simp only [misProgram,Nat.lt_irrefl,if_false]
    change (⟨_,0,i+1,_⟩ : MISState) = _
    congr 1
    exact greedy_bool_update H _ i v

lemma mis_correct {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (hinit : Proper H k.palette initial)
    (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    (∀ v w, misProgram.program.output H k ids initial (fun _ _ => false) v = true →
      misProgram.program.output H k ids initial (fun _ _ => false) w = true → ¬ H.Adj v w) ∧
    ∀ v, misProgram.program.output H k ids initial (fun _ _ => false) v = true ∨
      ∃ w, H.Adj v w ∧ misProgram.program.output H k ids initial (fun _ _ => false) w = true := by
  let col := colorProgram.program.output H k ids initial (fun _ _ => false)
  have hcol := colorProgram_correct H k ids initial hinit hD2 hD
  have hout (v : V) : misProgram.program.output H k ids initial (fun _ _ => false) v =
      decide (v ∈ greedy H col (k.degree^64)) := by
    change (misProgram.program.run H k ids initial (fun _ _ => false)
      (2*height k.palette+k.degree^64) v).selected = _
    rw [mis_greedy]
  constructor
  · intro v w hv hw
    rw [hout,decide_eq_true_eq] at hv hw
    exact greedy_independent H col hcol.2 _ v hv w hw
  · intro v
    rcases greedy_dominates H col _ v (hcol.1 v) with h | ⟨w,hw,hs⟩
    · exact Or.inl (by rw [hout,decide_eq_true_eq]; exact h)
    · exact Or.inr ⟨w,hw,by rw [hout,decide_eq_true_eq]; exact hs⟩

end BlockColorProof

-- Solutions/Sol_bipartite_runtime_parameters.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

lemma degreeLog_one (D : ℕ) : 1 ≤ degreeLog D := le_max_left _ _
lemma doubleLog_one (D : ℕ) : 1 ≤ doubleLog D := le_max_left _ _

lemma exponent_real_bound (D : ℕ) : (startExponent D:ℝ) ≤ 16*degreeLog D := by
  have hc := clog_real_bound D
  have hL := degreeLog_one D
  unfold startExponent initialExponent
  rw [Nat.cast_max]
  push_cast
  apply max_le <;> linarith

lemma stageCount_real_bound (D : ℕ) : (stageCount D:ℝ) ≤ 16*degreeLog D := by
  have hn : stageCount D ≤ startExponent D := by unfold stageCount; omega
  exact (show (stageCount D:ℝ) ≤ (startExponent D:ℝ) by exact_mod_cast hn).trans (exponent_real_bound D)

lemma length_real_bound (D : ℕ) : (blockLength D:ℝ) ≤ 2048*Real.sqrt (degreeLog D) := by
  have hL := degreeLog_one D
  have hK := exponent_real_bound D
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 256*Real.sqrt ((startExponent D:ℝ)+1) by positivity)).le
  change (blockLength D:ℝ) ≤ 256*Real.sqrt ((startExponent D:ℝ)+1)+1 at hceil
  have hrad : (startExponent D:ℝ)+1 ≤ 25*degreeLog D := by linarith
  have hroot := Real.sqrt_le_sqrt hrad
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 25)] at hroot
  norm_num at hroot
  have hs : 1 ≤ Real.sqrt (degreeLog D) := Real.one_le_sqrt.mpr hL
  linarith

lemma length_log_bound (D : ℕ) : 1 ≤ logTwo (blockLength D:ℝ) ∧
    logTwo (blockLength D:ℝ) ≤ 12*doubleLog D := by
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hlen := length_large D
  have hell : (2:ℝ) ≤ blockLength D := by exact_mod_cast hlen
  have hlow : 1 ≤ logTwo (blockLength D:ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by linarith)).mpr (by simpa using hell)
  have hsqrt : Real.sqrt (degreeLog D) ≤ degreeLog D := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hbound : (blockLength D:ℝ) ≤ 2048*degreeLog D := (length_real_bound D).trans (by linarith)
  have hlog : logTwo (blockLength D:ℝ) ≤ logTwo (2048*degreeLog D) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hbound
  have h2048 : logTwo 2048 = 11 := by
    change Real.logb 2 (2048:ℝ) = 11
    rw [show (2048:ℝ) = 2^11 by norm_num,Real.logb_pow]
    norm_num
  have hmul : logTwo (2048*degreeLog D) = 11+logTwo (degreeLog D) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) (by linarith : degreeLog D ≠ 0)]
    change logTwo 2048+logTwo (degreeLog D) = _
    rw [h2048]
    rfl
  rw [hmul] at hlog
  have hlogL : logTwo (degreeLog D) ≤ doubleLog D := le_max_right _ _
  exact ⟨hlow,by linarith⟩

lemma length_linear_bound (D : ℕ) : blockLength D ≤ 4096*(max 2 D) := by
  let X := max 2 D
  have hX : 2 ≤ X := le_max_left _ _
  have hc : Nat.clog 2 X ≤ X := (BlockColorProof.clog_lt_self X hX).le
  have hK : startExponent D ≤ 8*X := by
    unfold startExponent initialExponent
    change max 16 (Nat.clog 2 X+1+3) ≤ _
    apply max_le <;> omega
  have hs : Real.sqrt ((startExponent D:ℝ)+1) ≤ (startExponent D:ℝ)+1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by have h : 0 ≤ (startExponent D:ℝ) := Nat.cast_nonneg _; linarith))
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 256*Real.sqrt ((startExponent D:ℝ)+1) by positivity)).le
  change (blockLength D:ℝ) ≤ 256*Real.sqrt ((startExponent D:ℝ)+1)+1 at hceil
  have hKr : (startExponent D:ℝ) ≤ 8*(X:ℝ) := by exact_mod_cast hK
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hh : (blockLength D:ℝ) ≤ 4096*(X:ℝ) := by linarith
  exact_mod_cast hh

end BipartiteRounding

-- Solutions/Sol_bipartite_palette_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
open BlockColorProof

lemma height_le_clog (n : ℕ) : height n ≤ 1+Nat.clog 2 n := by
  rw [height]
  split_ifs with hn
  · omega
  · have h := height_le_self (Nat.clog 2 n)
    omega

lemma logStar_degree_bound (D : ℕ) : (logStar D:ℝ) ≤ doubleLog D+4 := by
  let X := max 2 D
  let c := Nat.clog 2 X
  have hX : 2 ≤ X := le_max_left _ _
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hc : (c:ℝ) ≤ degreeLog D+1 := clog_real_bound D
  have hpad : max 2 (c:ℝ) ≤ 2*degreeLog D := max_le (by linarith) (by linarith)
  have hlog : logTwo (max 2 (c:ℝ)) ≤ logTwo (2*degreeLog D) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith [le_max_left 2 (c:ℝ)]) hpad
  have hmul : logTwo (2*degreeLog D) = 1+logTwo (degreeLog D) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) (by linarith : degreeLog D ≠ 0)]
    norm_num
  rw [hmul] at hlog
  have hlogL : logTwo (degreeLog D) ≤ doubleLog D := le_max_right _ _
  have hLc : degreeLog c ≤ doubleLog D+1 := by
    unfold degreeLog
    apply max_le <;> linarith
  have hcc : (Nat.clog 2 c:ℝ) ≤ doubleLog D+2 := by
    have hh := clog_real_bound c
    have hm : (Nat.clog 2 c:ℝ) ≤ (Nat.clog 2 (max 2 c):ℝ) := by exact_mod_cast Nat.clog_mono_right 2 (le_max_right 2 c)
    linarith
  have hheight : logStar D ≤ 2+Nat.clog 2 c := by
    rw [←height_max_two]
    change height X ≤ _
    rw [height,dif_neg (by omega : ¬X ≤ 1)]
    change 1+height c ≤ 2+Nat.clog 2 c
    have hh := height_le_clog c
    omega
  have hcast : (logStar D:ℝ) ≤ 2+(Nat.clog 2 c:ℝ) := by exact_mod_cast hheight
  linarith

def paletteLogConstant (a : ℕ) : ℕ := 4096*a+9

lemma palette_logStar_bound (a D : ℕ) :
    (logStar (2*(max 2 D)^(a*blockLength D)):ℝ) ≤ (paletteLogConstant a:ℝ)*doubleLog D := by
  let X := max 2 D
  let Z := 2*X^(a*blockLength D)
  let k := 4096*a+1
  let c := k+2
  have hX : 2 ≤ X := le_max_left _ _
  have hclog : Nat.clog 2 X ≤ X := (clog_lt_self X hX).le
  have hell := length_linear_bound D
  have hprod : Nat.clog 2 X*blockLength D ≤ X*(4096*X) := Nat.mul_le_mul hclog hell
  have hExp : 1+Nat.clog 2 X*(a*blockLength D) ≤ k*X^2 := by
    have h := Nat.mul_le_mul_left a hprod
    have hXsq : 1 ≤ X^2 := by nlinarith
    dsimp [k]
    nlinarith
  have hk : k ≤ X^k := by
    exact (Nat.lt_pow_self (n:=k) (by decide : 1 < 2)).le.trans (Nat.pow_le_pow_left hX k)
  have hExp' : k*X^2 ≤ X^c := by
    dsimp [c]
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hk
  have hZ : Z ≤ 2^(X^c) := by
    calc
      Z ≤ 2*(2^Nat.clog 2 X)^(a*blockLength D) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) X) _)
      _ = 2^(1+Nat.clog 2 X*(a*blockLength D)) := by
        rw [pow_add,pow_one]
        exact congrArg (fun n : ℕ => 2*n) (pow_mul 2 (Nat.clog 2 X) (a*blockLength D)).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (hExp.trans hExp')
  have hZtwo : 2 ≤ Z := by
    have hp : 0 < X^(a*blockLength D) := pow_pos (by omega) _
    dsimp [Z]
    omega
  have hpow : 1 ≤ X^c := by have hp : 0 < X^c := pow_pos (by omega) _; omega
  have hh := height_mono hZ
  rw [height_pow_two (X^c) hpow] at hh
  have hp := height_power X c hX
  have hXheight : height X = logStar D := height_max_two D
  rw [hXheight] at hp
  have hZheight : height Z = logStar Z := by rw [←height_max_two,max_eq_right hZtwo]
  rw [hZheight] at hh
  have hNat : logStar Z ≤ logStar D+c+1 := by omega
  have hreal : (logStar Z:ℝ) ≤ (logStar D:ℝ)+(c:ℝ)+1 := by exact_mod_cast hNat
  have hstar := logStar_degree_bound D
  have hJ := doubleLog_one D
  change (logStar Z:ℝ) ≤ _
  unfold paletteLogConstant
  dsimp [c,k] at hreal
  push_cast at hreal ⊢
  have ha0 : 0 ≤ (a:ℝ) := Nat.cast_nonneg _
  nlinarith

end BipartiteRounding

-- Solutions/Sol_bipartite_time_domination.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def stageWork (a D : ℕ) : ℝ := (blockLength D:ℝ)*
  ((logTwo (blockLength D:ℝ))^2+logTwo (blockLength D:ℝ)*(logStar (2*(max 2 D)^(a*blockLength D)):ℝ)+1)

lemma degree_three_halves (D : ℕ) : (degreeLog D)^(3/2:ℝ) = degreeLog D*Real.sqrt (degreeLog D) := by
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add (by linarith [degreeLog_one D]),Real.rpow_one,←Real.sqrt_eq_rpow]

lemma stageWork_one (a D : ℕ) : 1 ≤ stageWork a D := by
  have hell : (2:ℝ) ≤ blockLength D := by exact_mod_cast length_large D
  have hl := (length_log_bound D).1
  have hS : 0 ≤ (logStar (2*(max 2 D)^(a*blockLength D)):ℝ) := Nat.cast_nonneg _
  unfold stageWork
  nlinarith [sq_nonneg (logTwo (blockLength D:ℝ)),mul_nonneg (by linarith : 0 ≤ logTwo (blockLength D:ℝ)) hS]

lemma total_stageWork_bound (a D : ℕ) :
    (stageCount D:ℝ)*stageWork a D ≤
      32768*(145+12*(paletteLogConstant a:ℝ))*(degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by
  let L := degreeLog D
  let J := doubleLog D
  let l := logTwo (blockLength D:ℝ)
  let S : ℝ := logStar (2*(max 2 D)^(a*blockLength D))
  let P : ℝ := paletteLogConstant a
  have hL : 1 ≤ L := degreeLog_one D
  have hJ : 1 ≤ J := doubleLog_one D
  have hl : 1 ≤ l := (length_log_bound D).1
  have hlup : l ≤ 12*J := (length_log_bound D).2
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hSup : S ≤ P*J := palette_logStar_bound a D
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hl0 : 0 ≤ l := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hlSq : l^2 ≤ 144*J^2 := by
    have hh := mul_self_le_mul_self hl0 hlup
    nlinarith
  have hcross : l*S ≤ 12*P*J^2 := by
    have hh := mul_le_mul hlup hSup hS (show 0 ≤ 12*J by positivity)
    nlinarith
  have hbracket : l^2+l*S+1 ≤ (145+12*P)*J^2 := by nlinarith
  have hbracket0 : 0 ≤ l^2+l*S+1 := by positivity
  have he := length_real_bound D
  have hn := stageCount_real_bound D
  have hwork : stageWork a D ≤ 2048*Real.sqrt L*((145+12*P)*J^2) :=
    mul_le_mul he hbracket hbracket0 (by positivity)
  have hprod := mul_le_mul hn hwork (show 0 ≤ stageWork a D from by linarith [stageWork_one a D])
    (show 0 ≤ 16*L by positivity)
  rw [degree_three_halves]
  change _ ≤ 32768*(145+12*P)*(L*Real.sqrt L)*J^2
  nlinarith

lemma time_basic_bounds (n D : ℕ) : 1 ≤ matchingTime n D ∧ degreeLog D ≤ matchingTime n D ∧
    Real.sqrt (degreeLog D)*(logStar n:ℝ) ≤ matchingTime n D := by
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hs : 1 ≤ Real.sqrt (degreeLog D) := Real.one_le_sqrt.mpr hL
  have hterm : degreeLog D ≤ (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by
    rw [degree_three_halves]
    have hJ2 : 1 ≤ (doubleLog D)^2 := by nlinarith
    have hh := mul_le_mul hs hJ2 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ Real.sqrt (degreeLog D))
    have hscaled := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ degreeLog D)
    nlinarith
  have hsecond : 0 ≤ Real.sqrt (degreeLog D)*(logStar n:ℝ) := by positivity
  have hfirst : 0 ≤ (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by positivity
  unfold matchingTime
  exact ⟨by linarith,by linarith,by linarith⟩

lemma time_domination (a n D : ℕ) (F Z B K : ℝ) (hF : 0 ≤ F) (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    F*degreeLog D+Z*(blockLength D:ℝ)*(logStar n:ℝ)+B*(stageCount D:ℝ)*stageWork a D+K ≤
      (F+2048*Z+32768*(145+12*(paletteLogConstant a:ℝ))*B+K)*matchingTime n D := by
  have ht := time_basic_bounds n D
  have hFterm := mul_le_mul_of_nonneg_left ht.2.1 hF
  have hZlen := mul_le_mul_of_nonneg_right (length_real_bound D) (show 0 ≤ (logStar n:ℝ) by positivity)
  have hZterm := mul_le_mul_of_nonneg_left (hZlen.trans
    (by nlinarith [ht.2.2] : 2048*Real.sqrt (degreeLog D)*(logStar n:ℝ) ≤ 2048*matchingTime n D)) hZ
  have hstage := total_stageWork_bound a D
  have htime : (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 ≤ matchingTime n D :=
    le_add_of_nonneg_right (by positivity)
  have hcoeff : 0 ≤ 32768*(145+12*(paletteLogConstant a:ℝ)) := by positivity
  have hstageTime : (stageCount D:ℝ)*stageWork a D ≤ 32768*(145+12*(paletteLogConstant a:ℝ))*matchingTime n D := by
    calc
      _ ≤ (32768*(145+12*(paletteLogConstant a:ℝ)))*((degreeLog D)^(3/2:ℝ)*(doubleLog D)^2) := by nlinarith [hstage]
      _ ≤ _ := mul_le_mul_of_nonneg_left htime hcoeff
  have hBterm := mul_le_mul_of_nonneg_left hstageTime hB
  have hKterm := mul_le_mul_of_nonneg_left ht.1 hK
  nlinarith

end BipartiteRounding

-- Solutions/Sol_booster_time_inflation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingBooster

lemma padded_product (n s : ℕ) : max 2 ((n+1)*s) ≤ (max 2 n)^(s+2) := by
  let X := max 2 n
  have hX : 2 ≤ X := le_max_left _ _
  have hn : n ≤ X := le_max_right _ _
  have hs : s ≤ X^s := (Nat.lt_pow_self (n:=s) (by decide : 1 < 2)).le.trans (Nat.pow_le_pow_left hX s)
  have hn1 : n+1 ≤ X^2 := by nlinarith
  have hprod := Nat.mul_le_mul hn1 hs
  have hpow : X^2*X^s = X^(s+2) := by rw [pow_add]; ring
  apply max_le
  · have hp : 1 ≤ X^s := by have h := pow_pos (show 0 < X by omega) s; omega
    rw [←hpow]
    nlinarith
  · exact hprod.trans_eq hpow

lemma logStar_product (n s : ℕ) : logStar ((n+1)*s) ≤ (s+3)*logStar n := by
  have h := (BlockColorProof.height_mono (padded_product n s)).trans
    (BlockColorProof.height_ID_bound n (s+2))
  rw [BlockColorProof.height_max_two] at h
  convert h using 1 <;> ring

lemma degreeLog_product (D s : ℕ) : degreeLog ((D+1)*s) ≤ ((s:ℝ)+2)*degreeLog D := by
  have hpow : ((max 2 ((D+1)*s):ℕ):ℝ) ≤ ((max 2 D:ℕ):ℝ)^(s+2) := by exact_mod_cast padded_product D s
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (show (0:ℝ) < (max 2 ((D+1)*s):ℕ) by exact_mod_cast (show 0 < max 2 ((D+1)*s) by omega)) hpow
  rw [Real.logb_pow] at hlog
  simp only [Nat.cast_max,Nat.cast_ofNat,Nat.cast_add] at hlog
  have hL := BipartiteRounding.degreeLog_one D
  have hsmall : logTwo (max 2 (D:ℝ)) ≤ degreeLog D := le_max_right _ _
  have hs : 0 ≤ (s:ℝ)+2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsmall hs
  change max 1 (logTwo (max 2 (((D+1)*s:ℕ):ℝ))) ≤ ((s:ℝ)+2)*degreeLog D
  apply max_le
  · nlinarith
  · change logTwo (max 2 (((D+1)*s:ℕ):ℝ)) ≤ _
    dsimp only [logTwo] at hm ⊢
    push_cast at hlog ⊢
    exact hlog.trans hm

lemma logTwo_nat_le (a : ℕ) (ha : 0 < a) : logTwo (a:ℝ) ≤ (a:ℝ) := by
  have hp : (a:ℝ) ≤ (2:ℝ)^a := by exact_mod_cast (Nat.lt_pow_self (n:=a) (by decide : 1 < 2)).le
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (Nat.cast_pos.mpr ha) hp
  simpa [logTwo,Real.logb_pow] using hl

lemma doubleLog_product (D s : ℕ) : doubleLog ((D+1)*s) ≤ ((s:ℝ)+3)*doubleLog D := by
  have hL := BipartiteRounding.degreeLog_one D
  have hL' := BipartiteRounding.degreeLog_one ((D+1)*s)
  have hJ := BipartiteRounding.doubleLog_one D
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by linarith : 0 < degreeLog ((D+1)*s))
    (degreeLog_product D s)
  rw [Real.logb_mul (by positivity : (s:ℝ)+2 ≠ 0) (by linarith : degreeLog D ≠ 0)] at hlog
  have ha := logTwo_nat_le (s+2) (by omega)
  push_cast at ha
  have hbase : logTwo (degreeLog D) ≤ doubleLog D := le_max_right _ _
  change max 1 (logTwo (degreeLog ((D+1)*s))) ≤ ((s:ℝ)+3)*doubleLog D
  apply max_le
  · nlinarith
  · change logTwo (degreeLog ((D+1)*s)) ≤ _
    dsimp only [logTwo] at ha hbase ⊢
    nlinarith

lemma time_generic (L L' J J' S S' a : ℝ) (ha : 1 ≤ a)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (hJ : 0 ≤ J) (hJ' : 0 ≤ J') (hS : 0 ≤ S) (hS' : 0 ≤ S')
    (hLu : L' ≤ a*L) (hJu : J' ≤ a*J) (hSu : S' ≤ a*S) :
    L'*Real.sqrt L'*J'^2+Real.sqrt L'*S' ≤ a^4*(L*Real.sqrt L*J^2+Real.sqrt L*S) := by
  have ha0 : 0 ≤ a := by linarith
  have hroot : Real.sqrt L' ≤ a*Real.sqrt L := by
    calc
      _ ≤ Real.sqrt (a*L) := Real.sqrt_le_sqrt hLu
      _ = Real.sqrt a*Real.sqrt L := Real.sqrt_mul ha0 _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr ha)) (Real.sqrt_nonneg _)
  have hJsq : J'^2 ≤ (a*J)^2 := by nlinarith [mul_self_le_mul_self hJ' hJu]
  have hLs := mul_le_mul hLu hroot (Real.sqrt_nonneg _) (mul_nonneg ha0 hL)
  have hfirst := mul_le_mul hLs hJsq (sq_nonneg J') (by positivity : 0 ≤ a*L*(a*Real.sqrt L))
  have hsecond := mul_le_mul hroot hSu hS' (by positivity : 0 ≤ a*Real.sqrt L)
  have haa : a^2 ≤ a^4 := by nlinarith [sq_nonneg (a^2-1)]
  have hsecond' := mul_le_mul_of_nonneg_right haa (mul_nonneg (Real.sqrt_nonneg L) hS)
  nlinarith

lemma matchingTime_product (n D s : ℕ) (hs : 1 ≤ s) :
    matchingTime ((n+1)*s) ((D+1)*s) ≤ 256*(s:ℝ)^4*matchingTime n D := by
  have hL := BipartiteRounding.degreeLog_one D
  have hL' := BipartiteRounding.degreeLog_one ((D+1)*s)
  have hJ := BipartiteRounding.doubleLog_one D
  have hJ' := BipartiteRounding.doubleLog_one ((D+1)*s)
  have hLu : degreeLog ((D+1)*s) ≤ ((s:ℝ)+3)*degreeLog D := by
    have hh := degreeLog_product D s
    nlinarith
  have hSu : (logStar ((n+1)*s):ℝ) ≤ ((s:ℝ)+3)*(logStar n:ℝ) := by
    exact_mod_cast logStar_product n s
  have hh := time_generic _ _ _ _ _ _ ((s:ℝ)+3) (by have hh : (0:ℝ) ≤ s := Nat.cast_nonneg s; linarith)
    (by linarith : 0 ≤ degreeLog D) (by linarith : 0 ≤ degreeLog ((D+1)*s))
    (by linarith : 0 ≤ doubleLog D) (by linarith : 0 ≤ doubleLog ((D+1)*s))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hLu (doubleLog_product D s) hSu
  rw [←BipartiteRounding.degree_three_halves,←BipartiteRounding.degree_three_halves] at hh
  change matchingTime ((n+1)*s) ((D+1)*s) ≤ ((s:ℝ)+3)^4*matchingTime n D at hh
  have hs' : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hp : ((s:ℝ)+3)^4 ≤ 256*(s:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (s:ℝ)+3) (by linarith : (s:ℝ)+3 ≤ 4*(s:ℝ)) 4
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_right hp (by linarith [(BipartiteRounding.time_basic_bounds n D).1]))

end MatchingBooster

-- Solutions/Sol_booster_accuracy.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingBooster

def index (epsilon : ℝ) : ℕ := max 2 ⌈1/epsilon⌉₊

lemma index_two (epsilon : ℝ) : 2 ≤ index epsilon := le_max_left _ _

lemma index_accuracy (epsilon : ℝ) (he : 0 < epsilon) : 1/(index epsilon:ℝ) ≤ epsilon := by
  have hq : (0:ℝ) < index epsilon := by exact_mod_cast (show 0 < index epsilon from by have h:=index_two epsilon;omega)
  have hr : 1/epsilon ≤ (index epsilon:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈1/epsilon⌉₊)
  apply (div_le_iff₀ hq).mpr
  have hh := mul_le_mul_of_nonneg_left hr he.le
  have hid : epsilon*(1/epsilon) = 1 := by field_simp
  rw [hid] at hh
  exact hh

lemma index_bound (epsilon : ℝ) (he : 0 < epsilon) : (index epsilon:ℝ)+1 ≤ 4*(1+1/epsilon) := by
  have hi : 0 < 1/epsilon := one_div_pos.mpr he
  have hc := (Nat.ceil_lt_add_one hi.le).le
  unfold index
  rw [Nat.cast_max]
  have hm : max (2:ℝ) (⌈1/epsilon⌉₊:ℝ) ≤ 1/epsilon+2 := max_le (by linarith) (by linarith)
  nlinarith

end MatchingBooster

-- Solutions/Sol_rounding_feasible.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_nonneg (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e) (v : Fin N) : 0 ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_nonneg (fun e _ => hx e)

lemma load_add (x d : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => x e+d e) v = load G x v+load G d v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [sum_add_distrib]

lemma edge_le_load (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (u v : Fin N) (hAdj : G.Adj u v) : x s(u,v) ≤ load G x u := by
  unfold load RandomOrderCRS.fracDegree
  apply single_le_sum (fun e _ => hx e)
  exact (G.mem_incidenceFinset u s(u,v)).mpr ⟨G.mem_edgeSet.mpr hAdj,by simp⟩

lemma double_load_bound (x y : Sym2 (Fin N) → ℝ) (hxy : ∀ e, y e ≤ 2*x e) (v : Fin N) :
    load G y v ≤ 2*load G x v := by
  unfold load RandomOrderCRS.fracDegree
  calc
    _ ≤ ∑ e ∈ G.incidenceFinset v, 2*x e := sum_le_sum (fun e _ => hxy e)
    _ = _ := (mul_sum ..).symm

lemma dominated_fractional (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hload : ∀ v, load G x v ≤ 1/2) (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 2*x e) :
    fractional G y ∧ ∀ v, load G y v ≤ 1 := by
  have hx0 : ∀ e, 0 ≤ x e := fun e => (hx.1 e).1
  have hyload (v : Fin N) : load G y v ≤ 1 := by
    have hh := double_load_bound G x y (fun e => (hy e).2) v
    have ht := hload v
    linarith
  have hsupport (e : Sym2 (Fin N)) (he : e ∉ G.edgeSet) : y e = 0 := by
    have hxz := hx.2.1 e he
    have hh := hy e
    rw [hxz] at hh
    linarith
  have hyupper (e : Sym2 (Fin N)) : y e ≤ 1 := by
    by_cases he : e ∈ G.edgeSet
    · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
      have hAdj := G.mem_edgeSet.mp he
      have hh := edge_le_load G x hx0 u v hAdj
      have ht := hload u
      have hb := (hy s(u,v)).2
      linarith
    · rw [hsupport e he]
      norm_num
  exact ⟨⟨fun e => ⟨(hy e).1,hyupper e⟩,hsupport,hyload⟩,hyload⟩

end MatchingRounding

-- Solutions/Sol_rounding_accumulation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

lemma quantum_sum (K n : ℕ) (hn : n ≤ K) :
    (∑ t ∈ range n, quantum (K-t)) = quantum (K-n)-quantum K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih (by omega)]
    have hk : K-n = (K-(n+1))+1 := by omega
    have hq := quantum_succ (K-(n+1))
    rw [←hk] at hq
    linarith

lemma quantum_sum_small (K n : ℕ) (hn : n+16 ≤ K) :
    (∑ t ∈ range n, quantum (K-t)) ≤ 1/65536 := by
  rw [quantum_sum K n (by omega)]
  have hq := quantum_antitone (show 16 ≤ K-n by omega)
  norm_num [quantum] at hq ⊢
  have hp : 0 ≤ ((2:ℝ)^K)⁻¹ := by positivity
  linarith

variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma fractional_of_load (x : Sym2 (Fin N) → ℝ) (hx : NonnegativeAssignment G x)
    (hload : ∀ v, load G x v ≤ 1/2) : fractional G x := by
  refine ⟨?_,hx.2,fun v => (hload v).trans (by norm_num)⟩
  intro e
  refine ⟨hx.1 e,?_⟩
  by_cases he : e ∈ G.edgeSet
  · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have hadj := G.mem_edgeSet.mp he
    have hh := MatchingRounding.edge_le_load G x hx.1 u v hadj
    linarith [hload u]
  · rw [hx.2 e he]
    norm_num

lemma stage_loss_bound (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hload : ∀ v, load G x v ≤ 1/2) (ell : ℝ) (hell : 0 < ell) (q : ℝ) (hq : 0 ≤ q)
    (hloss : potential G x-(8*penalty G x/ell^2+72*q*totalWeight G x) ≤ potential G y) :
    potential G x-(optimum G : ℝ)*(16/ell^2+72*q) ≤ potential G y := by
  have hw := halfload_weight_bound G x (fun e => (hx.1 e).1) hload
  have hp := halfload_penalty_bound G x (fun e => (hx.1 e).1) hload
  have hpen : penalty G x ≤ 2*(optimum G : ℝ) := hp.trans (by linarith)
  have hd : 0 < ell^2 := sq_pos_of_pos hell
  have hterm : 8*penalty G x/ell^2 ≤ 16*(optimum G : ℝ)/ell^2 :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hqterm : 72*q*totalWeight G x ≤ 72*q*(optimum G : ℝ) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have heq : (optimum G : ℝ)*(16/ell^2+72*q) = 16*(optimum G : ℝ)/ell^2+72*q*(optimum G : ℝ) := by ring
  rw [heq]
  linarith

lemma accumulated_loss (K n : ℕ) (ell : ℝ) (Phi : ℕ → ℝ) (O : ℝ)
    (hstep : ∀ t < n, Phi t-O*(16/ell^2+72*quantum (K-t)) ≤ Phi (t+1)) :
    Phi 0-O*(16*n/ell^2+72*∑ t ∈ range n, quantum (K-t)) ≤ Phi n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun t ht => hstep t (by omega))
    have hs := hstep n (by omega)
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring_nf at hi hs ⊢
    linarith

lemma accumulated_retention (K n ell : ℕ) (Phi : ℕ → ℝ) (O : ℝ) (hO : 0 ≤ O)
    (hn : n+16 ≤ K) (hell : 65536*(n:ℝ) ≤ (ell:ℝ)^2) (hellpos : 0 < ell)
    (hinit : O/128 ≤ Phi 0)
    (hstep : ∀ t < n, Phi t-O*(16/(ell:ℝ)^2+72*quantum (K-t)) ≤ Phi (t+1)) : O/256 ≤ Phi n := by
  have htotal := accumulated_loss K n ell Phi O hstep
  have hq := quantum_sum_small K n hn
  have hd : 0 < (ell:ℝ)^2 := by positivity
  have hdiv : 16*(n:ℝ)/(ell:ℝ)^2 ≤ 16/65536 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hsmall : 16*(n:ℝ)/(ell:ℝ)^2+72*(∑ t ∈ range n, quantum (K-t)) ≤ 1/256 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall hO
  linarith

end BipartiteRounding

-- Solutions/Sol_two_schedule.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

variable {V : Type} [Fintype V]

def TwoSchedule (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) : Prop :=
  (∀ u v, (∑ k, X u v k) = R u v) ∧
  (∀ u k, (∑ v, X u v k) ≤ 1) ∧ (∀ v k, (∑ u, X u v k) ≤ 1)

lemma two_schedule_exists (R : V → V → ℕ)
    (hrow : ∀ u, (∑ v, R u v) ≤ 2) (hcol : ∀ v, (∑ u, R u v) ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule R X := by
  let e := Fintype.equivFin V
  let matrix := fun i j => R (e.symm i) (e.symm j)
  have hr (i : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.rowSum matrix i ≤ 2 := by
    change (∑ j, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun v => R (e.symm i) v)]
    exact hrow _
  have hc (j : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.colSum matrix j ≤ 2 := by
    change (∑ i, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun u => R u (e.symm j))]
    exact hcol _
  obtain ⟨x,hx⟩ := (Timetabling85.ClassTeacher.prop_2_1 matrix 2).mpr ⟨hc,hr⟩
  refine ⟨fun u v k => x (e u) (e v) k,?_,?_,?_⟩
  · intro u v
    have hh := hx.1 (e u) (e v)
    simpa only [matrix,Equiv.symm_apply_apply] using hh
  · intro u k
    rw [e.sum_comp (fun j => x (e u) j k)]
    exact hx.2.1 (e u) k
  · intro v k
    rw [e.sum_comp (fun i => x i (e v) k)]
    exact hx.2.2.1 (e v) k

def scheduleSign (X : V → V → Fin 2 → ℕ) (u v : V) : ℝ := (X u v 0:ℝ)-(X u v 1:ℝ)

lemma scheduleSign_unit (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 1) : scheduleSign X u v = 1 ∨ scheduleSign X u v = -1 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have hcases : (X u v 0 = 1 ∧ X u v 1 = 0) ∨ (X u v 0 = 0 ∧ X u v 1 = 1) := by omega
  rcases hcases with h|h
  · left; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,sub_zero]
  · right; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,zero_sub]

lemma scheduleSign_row_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u : V) (hR : (∑ v, R u v) = 2) : (∑ v, scheduleSign X u v) = 0 := by
  have hs : (∑ v, X u v 0)+(∑ v, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ v, R u v := sum_congr rfl (fun v _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.1 u (0:Fin 2)
  have h1 := hX.2.1 u (1:Fin 2)
  have he0 : (∑ v, X u v 0) = 1 := by omega
  have he1 : (∑ v, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

lemma scheduleSign_col_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (v : V) (hR : (∑ u, R u v) = 2) : (∑ u, scheduleSign X u v) = 0 := by
  have hs : (∑ u, X u v 0)+(∑ u, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ u, R u v := sum_congr rfl (fun u _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.2 v (0:Fin 2)
  have h1 := hX.2.2 v (1:Fin 2)
  have he0 : (∑ u, X u v 0) = 1 := by omega
  have he1 : (∑ u, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

end MatchingRounding

-- Solutions/Sol_bipartite_signs.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Signs
variable {V : Type} [Fintype V] (H : SimpleGraph V) (side : V → Bool)

def bipartiteMatrix (u v : V) : ℕ := if H.Adj u v ∧ side u = false ∧ side v = true then 1 else 0

lemma adjacency_sum (v : V) : (∑ w, if H.Adj v w then (1:ℕ) else 0) = H.degree v := by
  rw [Finset.sum_boole]
  have he : univ.filter (H.Adj v) = H.neighborFinset v := by ext w; simp
  rw [he,H.card_neighborFinset_eq_degree]
  simp only [Nat.cast_id]

variable (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
include hSide

lemma bipartiteMatrix_row (u : V) (hu : side u = false) :
    (∑ v, bipartiteMatrix H side u v) = H.degree u := by
  have he (v : V) : bipartiteMatrix H side u v = if H.Adj u v then 1 else 0 := by
    by_cases hadj : H.Adj u v
    · have hv : side v = true := by have h := hSide u v hadj; cases hs : side v <;> simp_all
      simp only [bipartiteMatrix,hadj,hu,hv,and_self,ite_true]
    · simp only [bipartiteMatrix,hadj,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H u

lemma bipartiteMatrix_col (v : V) (hv : side v = true) :
    (∑ u, bipartiteMatrix H side u v) = H.degree v := by
  have he (u : V) : bipartiteMatrix H side u v = if H.Adj v u then 1 else 0 := by
    by_cases hadj : H.Adj v u
    · have hu : side u = false := by have h := hSide v u hadj; cases hs : side u <;> simp_all
      simp only [bipartiteMatrix,hadj,hadj.symm,hu,hv,and_self,ite_true]
    · have hn : ¬H.Adj u v := fun h => hadj h.symm
      simp only [bipartiteMatrix,hadj,hn,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H v

lemma graph_two_schedule (hD : ∀ v, H.degree v ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule (bipartiteMatrix H side) X := by
  apply two_schedule_exists
  · intro u
    cases hu : side u with
    | false => rw [bipartiteMatrix_row H side hSide u hu]; exact hD u
    | true => simp only [bipartiteMatrix,hu,Bool.true_eq_false,false_and,and_false,ite_false,sum_const_zero]; omega
  · intro v
    cases hv : side v with
    | false => simp only [bipartiteMatrix,hv,Bool.false_eq_true,and_false,ite_false,sum_const_zero]; omega
    | true => rw [bipartiteMatrix_col H side hSide v hv]; exact hD v

end Signs

section EdgeSigns
variable {V : Type} [Fintype V]

def signedEdge (side : V → Bool) (X : V → V → Fin 2 → ℕ) : Sym2 V → ℝ :=
  Sym2.lift ⟨(fun u v => if side u = side v then 0 else
    if side u = false then scheduleSign X u v else scheduleSign X v u),by
      intro u v
      cases hu : side u <;> cases hv : side v <;> simp only [hu,hv,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false]⟩

lemma signedEdge_apply (side : V → Bool) (X : V → V → Fin 2 → ℕ) (u v : V) :
    signedEdge side X s(u,v) = if side u = side v then 0 else
      if side u = false then scheduleSign X u v else scheduleSign X v u := rfl

lemma scheduleSign_zero (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 0) : scheduleSign X u v = 0 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have h0 : X u v 0 = 0 := by omega
  have h1 : X u v 1 = 0 := by omega
  simp only [scheduleSign,h0,h1,Nat.cast_zero,sub_zero]

lemma sum_neighbors_eq_all (H : SimpleGraph V) (v : V) (f g : V → ℝ)
    (hin : ∀ w, H.Adj v w → f w = g w) (hout : ∀ w, ¬H.Adj v w → g w = 0) :
    (∑ w ∈ H.neighborFinset v, f w) = ∑ w, g w := by
  have hn : H.neighborFinset v = univ.filter (H.Adj v) := by ext w; simp
  rw [hn,sum_filter]
  apply sum_congr rfl
  intro w hw
  by_cases hadj : H.Adj v w
  · rw [if_pos hadj,hin w hadj]
  · rw [if_neg hadj,hout w hadj]

variable (H : SimpleGraph V) (side : V → Bool)
    (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule (bipartiteMatrix H side) X)
include hSide hX

lemma signedEdge_unit (u v : V) (hAdj : H.Adj u v) :
    signedEdge side X s(u,v) = 1 ∨ signedEdge side X s(u,v) = -1 := by
  cases hu : side u with
  | false =>
    have hv : side v = true := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.false_eq_true,ite_false,ite_true]
    exact scheduleSign_unit _ X hX u v (by simp only [bipartiteMatrix,hAdj,hu,hv,and_self,ite_true])
  | true =>
    have hv : side v = false := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.true_eq_false,ite_false]
    exact scheduleSign_unit _ X hX v u (by simp only [bipartiteMatrix,hAdj.symm,hv,hu,and_self,ite_true])

lemma signedEdge_balanced (v : V) (hDegree : H.degree v = 2) :
    (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = 0 := by
  cases hv : side v with
  | false =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X v w := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = true := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.false_eq_true,ite_false,ite_true]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        simp only [bipartiteMatrix,hadj,false_and,ite_false]
    rw [he]
    exact scheduleSign_row_balance _ X hX v ((bipartiteMatrix_row H side hSide v hv).trans hDegree)
  | true =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X w v := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = false := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.true_eq_false,ite_false]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        have hn : ¬H.Adj w v := fun h => hadj h.symm
        simp only [bipartiteMatrix,hn,false_and,ite_false]
    rw [he]
    exact scheduleSign_col_balance _ X hX v ((bipartiteMatrix_col H side hSide v hv).trans hDegree)

end EdgeSigns

lemma bipartite_edge_signs {V : Type} [Fintype V] (H : SimpleGraph V)
    (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v) (hD : ∀ v, H.degree v ≤ 2) :
    ∃ z : Sym2 V → ℝ,
      (∀ u v, H.Adj u v → z s(u,v) = 1 ∨ z s(u,v) = -1) ∧
      (∀ v, H.degree v = 2 → (∑ w ∈ H.neighborFinset v, z s(v,w)) = 0) := by
  obtain ⟨X,hX⟩ := graph_two_schedule H side hSide hD
  exact ⟨signedEdge side X,signedEdge_unit H side hSide X hX,signedEdge_balanced H side hSide X hX⟩

end MatchingRounding

-- Solutions/Sol_restrict_edges.lean

open Classical Finset
noncomputable section
namespace MatchingRounding
section Restrict
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (S : Finset (Sym2 V))

def restrictEdges : SimpleGraph V where
  Adj a b := H.Adj a b ∧ s(a,b) ∈ S
  symm := ⟨by rintro a b ⟨h,he⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

lemma restrictEdges_le : restrictEdges H S ≤ H := fun _ _ h => h.1

lemma restrictEdges_edgeFinset (hS : S ⊆ H.edgeFinset) : (restrictEdges H S).edgeFinset = S := by
  ext e
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  change s(u,v) ∈ (restrictEdges H S).edgeFinset ↔ s(u,v) ∈ S
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  change (H.Adj u v ∧ s(u,v) ∈ S) ↔ s(u,v) ∈ S
  exact ⟨And.right,fun h => ⟨H.mem_edgeSet.mp (H.mem_edgeFinset.mp (hS h)),h⟩⟩

lemma restrictEdges_incidence (hS : S ⊆ H.edgeFinset) (v : V) :
    (restrictEdges H S).incidenceFinset v = S.filter (fun e => v ∈ e) := by
  rw [SimpleGraph.incidenceFinset_eq_filter,restrictEdges_edgeFinset H S hS]

lemma sum_incidence_neighbors (f : Sym2 V → ℝ) (v : V) :
    (∑ e ∈ H.incidenceFinset v, f e) = ∑ w ∈ H.neighborFinset v, f s(v,w) := by
  symm
  apply sum_bij (fun w _ => s(v,w))
  · intro w hw
    simpa using hw
  · intro a ha b hb hab
    exact Sym2.congr_right.mp hab
  · intro e he
    have hh := (H.mem_incidenceFinset v e).mp he
    obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hh.2
    exact ⟨w,by simpa using hh.1,rfl⟩
  · intro w hw
    rfl

lemma restrictEdges_signs (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (hD : ∀ v, H.degree v ≤ 2) (hS : S ⊆ H.edgeFinset) :
    ∃ z : Sym2 V → ℝ,
      (∀ e ∈ S, z e = 1 ∨ z e = -1) ∧
      ∀ v, (S.filter (fun e => v ∈ e)).card = 2 → (∑ e ∈ S.filter (fun e => v ∈ e), z e) = 0 := by
  let J := restrictEdges H S
  have hJSide : ∀ u v, J.Adj u v → side u ≠ side v := fun u v h => hSide u v h.1
  have hJD : ∀ v, J.degree v ≤ 2 := fun v => (J.degree_le_of_le (restrictEdges_le H S)).trans (hD v)
  obtain ⟨z,hz,hbal⟩ := bipartite_edge_signs J side hJSide hJD
  refine ⟨z,?_,?_⟩
  · intro e he
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have heJ : s(u,v) ∈ J.edgeFinset := by rwa [restrictEdges_edgeFinset H S hS]
    exact hz u v (J.mem_edgeSet.mp (J.mem_edgeFinset.mp heJ))
  · intro v hv
    have hd : J.degree v = 2 := by
      rw [←J.card_incidenceFinset_eq_degree,restrictEdges_incidence H S hS v]
      exact hv
    rw [←restrictEdges_incidence H S hS v,sum_incidence_neighbors]
    exact hbal v hd

end Restrict
end MatchingRounding

-- Solutions/Sol_dyadic_support.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

def DyadicLevels (x : Sym2 (Fin N) → ℝ) (K : ℕ) : Prop :=
  ∀ e, x e = 0 ∨ ∃ i ≤ K, x e = quantum i

lemma scaledDyadic_levels (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) : DyadicLevels (scaledDyadic G K f) (K+3) := by
  intro e
  by_cases he : e ∈ G.edgeSet
  · exact Or.inr ⟨dyadicIndex K (f e)+3,by have hh := dyadicIndex_spec K (f e) (hlower e he) (hf.1 e).2; omega,if_pos he⟩
  · exact Or.inl (if_neg he)

lemma rounding_levels (k : ℕ) (x y : Sym2 (Fin N) → ℝ) (hlevel : DyadicLevels x (k+1))
    (hx : fractional G x) (hy : fractional G y)
    (hround : ∀ e ∈ G.edgeSet, (x e = quantum (k+1) → y e = 0 ∨ y e = 2*quantum (k+1)) ∧
      (x e ≠ quantum (k+1) → y e = x e)) : DyadicLevels y k := by
  intro e
  by_cases he : e ∈ G.edgeSet
  · by_cases hactive : x e = quantum (k+1)
    · rcases (hround e he).1 hactive with hz|hz
      · exact Or.inl hz
      · exact Or.inr ⟨k,le_rfl,hz.trans (quantum_succ k).symm⟩
    · rw [(hround e he).2 hactive]
      rcases hlevel e with hz|⟨i,hi,heq⟩
      · exact Or.inl hz
      · have hik : i ≠ k+1 := fun h => hactive (h ▸ heq)
        exact Or.inr ⟨i,by omega,heq⟩
  · exact Or.inl (hy.2.1 e he)

lemma cleanup_levels (k : ℕ) (x : Sym2 (Fin N) → ℝ) (hlevel : DyadicLevels x k) :
    DyadicLevels (cleanup G x) k := by
  intro e
  unfold cleanup
  split_ifs
  · exact Or.inl rfl
  · exact hlevel e

def supportGraph (x : Sym2 (Fin N) → ℝ) : SimpleGraph (Fin N) where
  Adj u v := G.Adj u v ∧ x s(u,v) ≠ 0
  symm := ⟨by rintro u v ⟨h,hx⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using hx⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

lemma supportGraph_le (x : Sym2 (Fin N) → ℝ) : supportGraph G x ≤ G := fun _ _ h => h.1

lemma support_edgeFinset (x : Sym2 (Fin N) → ℝ) :
    (supportGraph G x).edgeFinset = G.edgeFinset.filter (fun e => x e ≠ 0) := by
  ext e
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,mem_filter]
  rfl

lemma support_weight (x : Sym2 (Fin N) → ℝ) : totalWeight (supportGraph G x) x = totalWeight G x := by
  unfold totalWeight
  rw [support_edgeFinset,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases he : x e = 0 <;> simp [he]

lemma support_degree (x : Sym2 (Fin N) → ℝ) (hx : fractional G x) (hlevels : DyadicLevels x 16) :
    ∀ v, (supportGraph G x).degree v ≤ 65536 := by
  intro v
  let H := supportGraph G x
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (SimpleGraph.mem_neighborFinset G v w).mpr ((SimpleGraph.mem_neighborFinset H v w).mp hw).1
  have hlower (w : Fin N) (hw : w ∈ H.neighborFinset v) : (1/65536:ℝ) ≤ x s(v,w) := by
    have hn := ((SimpleGraph.mem_neighborFinset H v w).mp hw).2
    rcases hlevels s(v,w) with hz|⟨i,hi,heq⟩
    · exact (hn hz).elim
    · rw [heq]
      exact (by norm_num [quantum] : (1/65536:ℝ) = quantum 16) ▸ quantum_antitone hi
  have hbound : (H.degree v : ℝ)/65536 ≤ load G x v := by
    calc
      _ = ∑ _ ∈ H.neighborFinset v, (1/65536:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ w ∈ H.neighborFinset v, x s(v,w) := sum_le_sum hlower
      _ ≤ ∑ w ∈ G.neighborFinset v, x s(v,w) := sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => (hx.1 s(v,w)).1)
      _ = load G x v := (MatchingRounding.sum_incidence_neighbors G x v).symm
  have hload := hx.2.2 v
  change load G x v ≤ 1 at hload
  have hcast : (H.degree v : ℝ) ≤ 65536 := by linarith
  exact_mod_cast hcast

end BipartiteRounding

-- Solutions/Sol_integral_extraction.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

def edgeGraph (M : Finset G.edgeSet) : SimpleGraph (Fin N) :=
  MatchingRounding.restrictEdges G (M.image Subtype.val)

lemma edgeGraph_edgeFinset (M : Finset G.edgeSet) : (edgeGraph G M).edgeFinset = M.image Subtype.val := by
  apply MatchingRounding.restrictEdges_edgeFinset
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  exact G.mem_edgeFinset.mpr f.property

lemma edgeGraph_matching (M : Finset G.edgeSet) (hM : SemiStreamMWM.IsMatching G M) : Matching G (edgeGraph G M) := by
  refine ⟨MatchingRounding.restrictEdges_le _ _,?_⟩
  intro e he f hf hne v hve hvf
  have heG : e.val ∈ M.image Subtype.val := by
    rw [←edgeGraph_edgeFinset G M]
    exact (edgeGraph G M).mem_edgeFinset.mpr e.property
  have hfG : f.val ∈ M.image Subtype.val := by
    rw [←edgeGraph_edgeFinset G M]
    exact (edgeGraph G M).mem_edgeFinset.mpr f.property
  obtain ⟨a,ha,hae⟩ := mem_image.mp heG
  obtain ⟨b,hb,hbf⟩ := mem_image.mp hfG
  have hab : a ≠ b := fun hh => hne (Subtype.ext (hae.symm.trans (hh ▸ hbf)))
  exact hM a ha b hb hab v (hae ▸ hve) (hbf ▸ hvf)

lemma edgeGraph_size (M : Finset G.edgeSet) : matchingSize (edgeGraph G M) = M.card := by
  unfold matchingSize
  rw [edgeGraph_edgeFinset,card_image_of_injective _ Subtype.val_injective]

lemma covering_weight_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1) (M : Finset G.edgeSet)
    (hcover : ∀ e : G.edgeSet, ∃ f ∈ M, ∃ v, v ∈ e.val ∧ v ∈ f.val) :
    totalWeight G x ≤ 2*(M.card:ℝ) := by
  let S := M.biUnion (fun e => e.val.toFinset)
  have hc : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨f,hf,v,hve,hvf⟩ := hcover ⟨e,he⟩
    exact ⟨v,mem_biUnion.mpr ⟨f,hf,Sym2.mem_toFinset.mpr hvf⟩,hve⟩
  have hw := weight_vertex_cover G x hx S hc
  have hsum : (∑ v ∈ S, load G x v) ≤ (S.card:ℝ) := by
    calc
      _ ≤ ∑ _ ∈ S, (1:ℝ) := sum_le_sum (fun v _ => hload v)
      _ = _ := by simp
  have hs : S.card ≤ 2*M.card := by
    calc
      _ ≤ ∑ e ∈ M, e.val.toFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, (2:ℕ) := sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega)
      _ = _ := by simp [mul_comm]
  have hcast : (S.card:ℝ) ≤ 2*(M.card:ℝ) := by exact_mod_cast hs
  linarith

lemma support_load (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load (supportGraph G x) x v = load G x v := by
  unfold load RandomOrderCRS.fracDegree
  rw [SimpleGraph.incidenceFinset_eq_filter,SimpleGraph.incidenceFinset_eq_filter,support_edgeFinset]
  rw [filter_filter]
  simp only [sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hz : x e = 0 <;> by_cases hv : v ∈ e <;> simp [hz,hv]

lemma integral_extraction (x : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hpotential : (optimum G:ℝ)/256 ≤ potential G x)
    (M : Finset (supportGraph G x).edgeSet)
    (hM : SemiStreamMWM.IsMatching (supportGraph G x) M)
    (hcover : ∀ e : (supportGraph G x).edgeSet, ∃ f ∈ M, ∃ v, v ∈ e.val ∧ v ∈ f.val) :
    Matching G (edgeGraph (supportGraph G x) M) ∧
      (optimum G:ℝ)/512 ≤ (matchingSize (edgeGraph (supportGraph G x) M):ℝ) := by
  have hmatch := edgeGraph_matching (supportGraph G x) M hM
  refine ⟨⟨hmatch.1.trans (supportGraph_le G x),hmatch.2⟩,?_⟩
  have hload : ∀ v, load (supportGraph G x) x v ≤ 1 := by
    intro v
    rw [support_load]
    exact hx.2.2 v
  have hw := covering_weight_bound (supportGraph G x) x (fun e => (hx.1 e).1) hload M hcover
  rw [support_weight] at hw
  have hpen : 0 ≤ penalty G x := mul_nonneg (by norm_num) (sum_nonneg (fun v _ => sq_nonneg (load G x v)))
  unfold potential at hpotential
  rw [edgeGraph_size]
  linarith

end BipartiteRounding

-- Solutions/Sol_local_pairing.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalPairing
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def pairs : List V → List (Finset V)
  | [] => []
  | [a] => [{a}]
  | a::b::rest => {a,b}::pairs rest

lemma pairs_map (f : V → W) (l : List V) :
    pairs (l.map f) = (pairs l).map (Finset.image f) := by
  fun_induction pairs l <;> simp_all [pairs]

lemma mem_pairs (l : List V) (v : V) :
    (∃ g ∈ pairs l, v ∈ g) ↔ v ∈ l := by
  fun_induction pairs l <;> simp_all [pairs,or_assoc]

lemma group_subset (l : List V) (g : Finset V) (hg : g ∈ pairs l) : ∀ v ∈ g, v ∈ l :=
  fun v hv => (mem_pairs l v).mp ⟨g,hg,hv⟩

lemma group_sizes (l : List V) (hn : l.Nodup) : ∀ g ∈ pairs l, g.card = 1 ∨ g.card = 2 := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl h))
    have hrest : rest.Nodup := hn.of_cons.of_cons
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact Or.inr (card_pair hab)
    · exact ih hrest g hg

lemma groups_disjoint (l : List V) (hn : l.Nodup) : (pairs l).Pairwise Disjoint := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have ha : a ∉ rest := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inr h))
    have hb : b ∉ rest := (List.nodup_cons.mp hn.of_cons).1
    have hrest : rest.Nodup := hn.of_cons.of_cons
    apply List.pairwise_cons.mpr
    constructor
    · intro g hg
      apply Finset.disjoint_left.mpr
      intro v hv hvg
      rcases mem_insert.mp hv with hva|hv
      · subst v
        exact ha (group_subset rest g hg a hvg)
      · have hvb : v = b := mem_singleton.mp hv
        exact hb (hvb ▸ group_subset rest g hg v hvg)
    · exact ih hrest

lemma singleton_pairwise (l : List V) (hn : l.Nodup) :
    (pairs l).Pairwise (fun g h => g.card ≠ 1 ∨ h.card ≠ 1) := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl h))
    have hrest : rest.Nodup := hn.of_cons.of_cons
    apply List.pairwise_cons.mpr
    exact ⟨fun g _ => Or.inl (by rw [card_pair hab]; norm_num),ih hrest⟩

lemma disjoint_index_unique (L : List (Finset V)) (hL : L.Pairwise Disjoint)
    (i j : Fin L.length) (v : V) (hi : v ∈ L.get i) (hj : v ∈ L.get j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact Finset.disjoint_left.mp (hL.rel_get_of_lt hlt) hi hj
  · exact Finset.disjoint_left.mp (hL.rel_get_of_lt hgt) hj hi

lemma singleton_index_unique (L : List (Finset V))
    (hL : L.Pairwise (fun g h => g.card ≠ 1 ∨ h.card ≠ 1))
    (i j : Fin L.length) (hi : (L.get i).card = 1) (hj : (L.get j).card = 1) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact (hL.rel_get_of_lt hlt).elim (fun h => h hi) (fun h => h hj)
  · exact (hL.rel_get_of_lt hgt).elim (fun h => h hj) (fun h => h hi)

lemma unique_group (l : List V) (hn : l.Nodup) (v : V) :
    v ∈ l ↔ ∃! i : Fin (pairs l).length, v ∈ (pairs l).get i := by
  constructor
  · intro hv
    obtain ⟨g,hg,hvg⟩ := (mem_pairs l v).mpr hv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    have hvi : v ∈ (pairs l).get i := by rw [hi]; exact hvg
    refine ⟨i,hvi,?_⟩
    intro j hj
    exact disjoint_index_unique _ (groups_disjoint l hn) j i v hj hvi
  · rintro ⟨i,hi,huniq⟩
    exact (mem_pairs l v).mp ⟨_,List.get_mem _ _,hi⟩

lemma singleton_bound (l : List V) (hn : l.Nodup) :
    ((univ : Finset (Fin (pairs l).length)).filter (fun i => ((pairs l).get i).card = 1)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  exact singleton_index_unique _ (singleton_pairwise l hn) i j (mem_filter.mp hi).2 (mem_filter.mp hj).2

end LocalPairing

-- Solutions/Sol_pairing_construction.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalPairing
section Sorted
variable {V : Type} [DecidableEq V] (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)

def sortedBy : List V := by
  letI := LinearOrder.lift' key hi
  exact S.sort

lemma sortedBy_nodup : (sortedBy S key hi).Nodup := by
  unfold sortedBy
  exact sort_nodup _ _

lemma mem_sortedBy (v : V) : v ∈ sortedBy S key hi ↔ v ∈ S := by
  unfold sortedBy
  exact Finset.mem_sort _

set_option backward.isDefEq.respectTransparency false in
lemma map_sortedBy : (sortedBy S key hi).map key = (S.image key).sort := by
  letI := LinearOrder.lift' key hi
  change S.sort.map key = (S.image key).sort
  have h := Finset.map_sort ⟨key,hi⟩ S (fun a b : V => a ≤ b) (fun a b : ℕ => a ≤ b)
    (fun _ _ _ _ => Iff.rfl)
  rw [Finset.map_eq_image] at h
  convert h using 1 <;> rfl

end Sorted

variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids)

def active (v : Fin N) : Finset (Fin N) := (G.neighborFinset v).filter (fun w => x s(v,w) = q)

def pairing : Pairing N := fun v => pairs (sortedBy (active G x q v) ids hi)

lemma pairing_valid : ValidPairing G x q (pairing G x q ids hi) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    exact group_sizes _ (sortedBy_nodup _ ids hi) (group _ a) (List.get_mem _ _)
  · intro v w
    have hmem : (G.Adj v w ∧ x s(v,w) = q) ↔ w ∈ sortedBy (active G x q v) ids hi := by
      rw [mem_sortedBy]
      simp only [active,mem_filter,SimpleGraph.mem_neighborFinset]
    exact hmem.trans (unique_group _ (sortedBy_nodup _ ids hi) w)
  · intro a w hw
    have hm := group_subset _ (group (pairing G x q ids hi) a) (List.get_mem _ _) w hw
    rw [mem_sortedBy] at hm
    exact ⟨(SimpleGraph.mem_neighborFinset G a.1 w).mp (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
  · intro v
    exact singleton_bound _ (sortedBy_nodup _ ids hi)

def localGroups (q : ℝ) (neighbors : Finset ℕ) (values : ℕ → ℝ) : List (Finset ℕ) :=
  pairs ((neighbors.filter (fun j => values j = q)).sort)

lemma localGroups_correct (out : Fin N → ℕ → ℝ) (hout : ReportsWeights G ids out x) (v : Fin N) :
    localGroups q (neighborIDs G ids v) (out v) = (pairing G x q ids hi v).map (image ids) := by
  have hactive : (neighborIDs G ids v).filter (fun j => out v j = q) = (active G x q v).image ids := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjneigh,hjval⟩ := mem_filter.mp hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hjneigh
      have hAdj := (SimpleGraph.mem_neighborFinset G v w).mp hw
      rw [(hout.2 v w hAdj).1] at hjval
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hjval⟩,rfl⟩
    · intro hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      have hAdj := (SimpleGraph.mem_neighborFinset G v w).mp (mem_filter.mp hw).1
      refine mem_filter.mpr ⟨mem_image.mpr ⟨w,(mem_filter.mp hw).1,rfl⟩,?_⟩
      rw [(hout.2 v w hAdj).1]
      exact (mem_filter.mp hw).2
  unfold localGroups pairing
  rw [hactive,←map_sortedBy _ ids hi,pairs_map]

end LocalPairing

-- Solutions/Sol_bipartite_proposals.lean

open Classical Finset
noncomputable section
namespace BipartiteProposals
section Selection
variable {V : Type} [DecidableEq V] (ids : V → ℕ) (hi : Function.Injective ids)

def least (S : Finset V) : Option V := (LocalPairing.sortedBy S ids hi).head?

lemma least_mem (S : Finset V) (v : V) (hv : least ids hi S = some v) : v ∈ S := by
  apply (LocalPairing.mem_sortedBy S ids hi v).mp
  have hmem : v ∈ least ids hi S := by rw [hv]; exact Option.mem_def.mpr rfl
  exact List.mem_of_mem_head? hmem

lemma least_complete (S : Finset V) (hS : S.Nonempty) : ∃ v, least ids hi S = some v := by
  cases h : least ids hi S with
  | none =>
    have he : LocalPairing.sortedBy S ids hi = [] := List.head?_eq_none_iff.mp h
    obtain ⟨v,hv⟩ := hS
    have hv' := (LocalPairing.mem_sortedBy S ids hi v).mpr hv
    rw [he] at hv'
    exact (List.not_mem_nil hv').elim
  | some v => exact ⟨v,rfl⟩

lemma least_named (S : Finset V) : (least ids hi S).map ids = (S.image ids).sort.head? := by
  rw [least,←List.head?_map,LocalPairing.map_sortedBy]

end Selection

section Proposals
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids)

def Free (M : SimpleGraph V) (v : V) : Prop := ∀ w, ¬M.Adj v w

def freeNeighbors (M : SimpleGraph V) (v : V) : Finset V := (H.neighborFinset v).filter (Free M)

def propose (M : SimpleGraph V) (v : V) : Option V :=
  if Free M v ∧ side v = false then least ids hi (freeNeighbors H M v) else none

def accept (M : SimpleGraph V) (w : V) : Option V :=
  if Free M w ∧ side w = true then least ids hi (univ.filter (fun v => propose H side ids hi M v = some w)) else none

def Chosen (M : SimpleGraph V) (u v : V) : Prop :=
  propose H side ids hi M u = some v ∧ accept H side ids hi M v = some u

include hside in
lemma propose_spec (M : SimpleGraph V) (u v : V) (h : propose H side ids hi M u = some v) :
    Free M u ∧ Free M v ∧ H.Adj u v ∧ side u = false ∧ side v = true := by
  unfold propose at h
  split_ifs at h with hu
  · have hm := least_mem ids hi _ v h
    have hAdj := (SimpleGraph.mem_neighborFinset H u v).mp (mem_filter.mp hm).1
    have hneq := hside u v hAdj
    have hv : side v = true := by cases hvs : side v <;> simp_all
    exact ⟨hu.1,(mem_filter.mp hm).2,hAdj,hu.2,hv⟩

lemma accept_spec (M : SimpleGraph V) (u v : V) (h : accept H side ids hi M v = some u) :
    Chosen H side ids hi M u v := by
  unfold accept at h
  split_ifs at h with hv
  · have hm := least_mem ids hi _ u h
    exact ⟨(mem_filter.mp hm).2,by unfold accept; rw [if_pos hv]; exact h⟩

lemma propose_complete (M : SimpleGraph V) (v : V) (hv : Free M v) (hleft : side v = false)
    (hn : (freeNeighbors H M v).Nonempty) : ∃ w, propose H side ids hi M v = some w := by
  unfold propose
  rw [if_pos ⟨hv,hleft⟩]
  exact least_complete ids hi _ hn

include hside in
lemma accept_complete (M : SimpleGraph V) (u v : V) (hu : propose H side ids hi M u = some v) :
    ∃ w, accept H side ids hi M v = some w := by
  have hp := propose_spec H side hside ids hi M u v hu
  unfold accept
  rw [if_pos ⟨hp.2.1,hp.2.2.2.2⟩]
  exact least_complete ids hi _ ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩⟩

end Proposals
end BipartiteProposals

-- Solutions/Sol_matching_mate.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProposals
variable {V : Type} [Fintype V] [DecidableEq V]
    (ids : V → ℕ) (hi : Function.Injective ids) (M : SimpleGraph V)

def mate (v : V) : Option V := least ids hi (M.neighborFinset v)

lemma mate_some (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) (u v : V) :
    mate ids hi M u = some v ↔ M.Adj u v := by
  constructor
  · intro h
    exact (SimpleGraph.mem_neighborFinset M u v).mp (least_mem ids hi _ v h)
  · intro h
    obtain ⟨w,hw⟩ := least_complete ids hi (M.neighborFinset u)
      ⟨v,(SimpleGraph.mem_neighborFinset M u v).mpr h⟩
    have huw := (SimpleGraph.mem_neighborFinset M u w).mp (least_mem ids hi _ w hw)
    have heq := hM u w v huw h
    exact hw.trans (congrArg some heq)

lemma mate_none (u : V) : mate ids hi M u = none ↔ Free M u := by
  constructor
  · intro h w hw
    obtain ⟨v,hv⟩ := least_complete ids hi (M.neighborFinset u)
      ⟨w,(SimpleGraph.mem_neighborFinset M u w).mpr hw⟩
    change mate ids hi M u = some v at hv
    rw [h] at hv
    cases hv
  · intro h
    cases hm : mate ids hi M u with
    | none => rfl
    | some v =>
      have hv := (SimpleGraph.mem_neighborFinset M u v).mp (least_mem ids hi _ v hm)
      exact (h v hv).elim

lemma unique_graph_matching {N : ℕ} (G M : SimpleGraph (Fin N)) (hsub : M ≤ G)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) : Matching G M := by
  refine ⟨hsub,?_⟩
  intro e he f hf hne v hve hvf
  obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp hve
  obtain ⟨w,hw⟩ := Sym2.mem_iff_exists.mp hvf
  have hvu : M.Adj v u := M.mem_edgeSet.mp (by rw [←hu]; exact e.property)
  have hvw : M.Adj v w := M.mem_edgeSet.mp (by rw [←hw]; exact f.property)
  have heq := hM v u w hvu hvw
  exact hne (Subtype.ext (hu.trans ((congrArg (fun z => s(v,z)) heq).trans hw.symm)))

lemma named_mate_reports {N : ℕ} (G M : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (hsub : M ≤ G)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) :
    ReportsMatching G ids (fun v => (mate ids hi M v).map ids) M := by
  refine ⟨unique_graph_matching G M hsub hM,?_⟩
  intro v
  constructor
  · rw [Option.map_eq_none_iff,mate_none]
    rfl
  · intro j
    constructor
    · intro h
      obtain ⟨w,hw,hj⟩ := Option.map_eq_some_iff.mp h
      exact ⟨w,(mate_some ids hi M hM v w).mp hw,hj⟩
    · rintro ⟨w,hw,hj⟩
      dsimp only
      rw [(mate_some ids hi M hM v w).mpr hw]
      exact congrArg some hj

end BipartiteProposals

-- Solutions/Sol_double_cover_basic.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover
variable {N : ℕ}

abbrev Copies (N : ℕ) := Fin N ⊕ Fin N

def owner : Copies N → Fin N := Sum.elim id id

def side : Copies N → Bool
  | .inl _ => false
  | .inr _ => true

def identity (ids : Fin N → ℕ) : Copies N → ℕ
  | .inl v => 2*ids v
  | .inr v => 2*ids v+1

lemma identity_injective (ids : Fin N → ℕ) (hi : Function.Injective ids) : Function.Injective (identity ids) := by
  intro a b hab
  cases a with
  | inl u =>
    cases b with
    | inl v => have h : ids u = ids v := by change 2*ids u = 2*ids v at hab; omega
               exact congrArg Sum.inl (hi h)
    | inr v => change 2*ids u = 2*ids v+1 at hab; omega
  | inr u =>
    cases b with
    | inl v => change 2*ids u+1 = 2*ids v at hab; omega
    | inr v => have h : ids u = ids v := by change 2*ids u+1 = 2*ids v+1 at hab; omega
               exact congrArg Sum.inr (hi h)

lemma owner_adj (G : SimpleGraph (Fin N)) (a b : Copies N) (h : G.bipartiteDoubleCover.Adj a b) : G.Adj (owner a) (owner b) := by
  cases a <;> cases b <;> simp_all [SimpleGraph.bipartiteDoubleCover,owner]

lemma cover_side (G : SimpleGraph (Fin N)) : ∀ a b, G.bipartiteDoubleCover.Adj a b → side a ≠ side b := by
  intro a b h
  cases a <;> cases b <;> simp_all [SimpleGraph.bipartiteDoubleCover,side]

lemma neighbors_left (G : SimpleGraph (Fin N)) (v : Fin N) :
    G.bipartiteDoubleCover.neighborFinset (.inl v) = (G.neighborFinset v).image Sum.inr := by
  ext w
  rw [SimpleGraph.mem_neighborFinset,mem_image]
  cases w <;> simp [SimpleGraph.mem_neighborFinset,SimpleGraph.bipartiteDoubleCover]

lemma neighbors_right (G : SimpleGraph (Fin N)) (v : Fin N) :
    G.bipartiteDoubleCover.neighborFinset (.inr v) = (G.neighborFinset v).image Sum.inl := by
  ext w
  rw [SimpleGraph.mem_neighborFinset,mem_image]
  cases w <;> simp [SimpleGraph.mem_neighborFinset,SimpleGraph.bipartiteDoubleCover]

lemma degree_cover (G : SimpleGraph (Fin N)) (a : Copies N) : G.bipartiteDoubleCover.degree a = G.degree (owner a) := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  cases a with
  | inl v => rw [neighbors_left,card_image_of_injective _ Sum.inr_injective,G.card_neighborFinset_eq_degree]; rfl
  | inr v => rw [neighbors_right,card_image_of_injective _ Sum.inl_injective,G.card_neighborFinset_eq_degree]; rfl

def indexEquiv : Fin (N+N) ≃ Copies N := finSumFinEquiv.symm

def coverGraph (G : SimpleGraph (Fin N)) : SimpleGraph (Fin (N+N)) := G.bipartiteDoubleCover.comap indexEquiv

def coverOwner (v : Fin (N+N)) : Fin N := owner (indexEquiv v)
def coverSide (v : Fin (N+N)) : Bool := side (indexEquiv v)
def coverIdentity (ids : Fin N → ℕ) (v : Fin (N+N)) : ℕ := identity ids (indexEquiv v)

lemma coverIdentity_injective (ids : Fin N → ℕ) (hi : Function.Injective ids) : Function.Injective (coverIdentity ids) :=
  (identity_injective ids hi).comp indexEquiv.injective

lemma coverGraph_bipartite (G : SimpleGraph (Fin N)) : Bipartition (coverGraph G) coverSide :=
  fun a b h => cover_side G (indexEquiv a) (indexEquiv b) h

lemma coverGraph_degree (G : SimpleGraph (Fin N)) (v : Fin (N+N)) :
    (coverGraph G).degree v = G.degree (coverOwner v) := by
  let f : coverGraph G ≃g G.bipartiteDoubleCover := SimpleGraph.Iso.comap indexEquiv G.bipartiteDoubleCover
  exact (f.degree_eq v).symm.trans (degree_cover G (indexEquiv v))

lemma coverGraph_card (G : SimpleGraph (Fin N)) : (coverGraph G).edgeFinset.card = 2*G.edgeFinset.card := by
  let f : coverGraph G ≃g G.bipartiteDoubleCover := SimpleGraph.Iso.comap indexEquiv G.bipartiteDoubleCover
  exact f.card_edgeFinset_eq.trans G.card_edgeFinset_bipartiteDoubleCover

lemma coverGraph_le (G M : SimpleGraph (Fin N)) (h : M ≤ G) : coverGraph M ≤ coverGraph G := by
  intro a b hab
  change M.bipartiteDoubleCover.Adj (indexEquiv a) (indexEquiv b) at hab
  change G.bipartiteDoubleCover.Adj (indexEquiv a) (indexEquiv b)
  generalize ha : indexEquiv a = u at hab ⊢
  generalize hb : indexEquiv b = v at hab ⊢
  cases u <;> cases v <;> simp_all [SimpleGraph.bipartiteDoubleCover]
  all_goals exact h hab

lemma matching_neighbor_unique (G M : SimpleGraph (Fin N)) (hM : Matching G M) :
    ∀ u v w, M.Adj u v → M.Adj u w → v = w := by
  intro u v w huv huw
  by_contra hne
  let e : M.edgeSet := ⟨s(u,v),M.mem_edgeSet.mpr huv⟩
  let f : M.edgeSet := ⟨s(u,w),M.mem_edgeSet.mpr huw⟩
  have hef : e ≠ f := by
    intro he
    exact hne (Sym2.congr_right.mp (congrArg Subtype.val he))
  exact hM.2 e (mem_univ _) f (mem_univ _) hef u (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)

lemma cover_neighbor_unique (M : SimpleGraph (Fin N))
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) :
    ∀ u v w : Copies N, M.bipartiteDoubleCover.Adj u v → M.bipartiteDoubleCover.Adj u w → v = w := by
  intro u v w huv huw
  cases u <;> cases v <;> cases w <;> simp_all [SimpleGraph.bipartiteDoubleCover]
  all_goals exact hM _ _ _ huv huw

lemma cover_matching (G M : SimpleGraph (Fin N)) (hM : Matching G M) : Matching (coverGraph G) (coverGraph M) := by
  apply BipartiteProposals.unique_graph_matching _ _ (coverGraph_le G M hM.1)
  intro u v w huv huw
  apply indexEquiv.injective
  exact cover_neighbor_unique M (matching_neighbor_unique G M hM) _ _ _ huv huw

end MatchingDoubleCover

-- Solutions/Sol_double_cover_optimum.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover
variable {N : ℕ}

lemma matching_size_le_optimum (G M : SimpleGraph (Fin N)) (hM : Matching G M) : matchingSize M ≤ optimum G := by
  let lift : M.edgeSet → G.edgeSet := fun e => ⟨e.val,SimpleGraph.edgeSet_mono hM.1 e.property⟩
  let E : Finset G.edgeSet := univ.image lift
  have hi : Function.Injective lift := fun e f h => Subtype.ext (congrArg (fun e : G.edgeSet => e.val) h)
  have hE : SemiStreamMWM.IsMatching G E := by
    intro e he f hf hne v hve hvf
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
    exact hM.2 a (mem_univ _) b (mem_univ _) (fun h => hne (congrArg lift h)) v hve hvf
  have hc : E.card = matchingSize M := by
    unfold E
    rw [card_image_of_injective _ hi,card_univ,M.card_edgeSet]
    rfl
  have hle : E.card ≤ optimum G :=
    le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_univ _,hE⟩)
  rwa [hc] at hle

lemma maximum_graph (G : SimpleGraph (Fin N)) : ∃ M : SimpleGraph (Fin N), Matching G M ∧ matchingSize M = optimum G := by
  obtain ⟨E,hE,hcard⟩ := BipartiteRounding.maximum_matching G
  refine ⟨BipartiteRounding.edgeGraph G E,BipartiteRounding.edgeGraph_matching G E hE,?_⟩
  rw [BipartiteRounding.edgeGraph_size,hcard]

lemma cover_optimum (G : SimpleGraph (Fin N)) : 2*optimum G ≤ optimum (coverGraph G) := by
  obtain ⟨M,hM,hsize⟩ := maximum_graph G
  have hle := matching_size_le_optimum (coverGraph G) (coverGraph M) (cover_matching G M hM)
  have hcard : matchingSize (coverGraph M) = 2*matchingSize M := coverGraph_card M
  rw [hcard,hsize] at hle
  exact hle

lemma cover_identifiers (n b : ℕ) (ids : Fin N → ℕ) (hid : Identifiers n (b+1) ids) :
    Identifiers (n+n) (b+2) (coverIdentity ids) := by
  refine ⟨coverIdentity_injective ids hid.1,?_⟩
  intro a
  let X := max 2 n
  let Y := max 2 (n+n)
  have hXY : X ≤ Y := max_le_max_left _ (by omega)
  have hY : 2 ≤ Y := le_max_left _ _
  have hp : 2*X^(b+1) ≤ Y^(b+2) := by
    have h := Nat.mul_le_mul hY (Nat.pow_le_pow_left hXY (b+1))
    conv_rhs => rw [show b+2 = (b+1)+1 by omega,pow_succ]
    simpa only [mul_comm] using h
  apply lt_of_lt_of_le _ hp
  change identity ids (indexEquiv a) < 2*X^(b+1)
  generalize he : indexEquiv a = v
  cases v with
  | inl v =>
    have hv : ids v < X^(b+1) := hid.2 v
    change 2*ids v < 2*X^(b+1)
    omega
  | inr v =>
    have hv : ids v < X^(b+1) := hid.2 v
    change 2*ids v+1 < 2*X^(b+1)
    omega

lemma cover_bounded (G : SimpleGraph (Fin N)) (n D : ℕ) (h : boundedGraph G n D) :
    boundedGraph (coverGraph G) (n+n) D := by
  constructor
  · have hN := h.1
    omega
  · intro v
    rw [coverGraph_degree]
    exact h.2 (coverOwner v)

end MatchingDoubleCover

-- Solutions/Sol_double_cover_routing.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover
variable {N : ℕ}

def left (v : Fin N) : Fin (N+N) := indexEquiv.symm (.inl v)
def right (v : Fin N) : Fin (N+N) := indexEquiv.symm (.inr v)

@[simp] lemma index_left (v : Fin N) : indexEquiv (left v) = .inl v := indexEquiv.apply_symm_apply _
@[simp] lemma index_right (v : Fin N) : indexEquiv (right v) = .inr v := indexEquiv.apply_symm_apply _
@[simp] lemma owner_left (v : Fin N) : coverOwner (left v) = v := by simp [coverOwner,owner]
@[simp] lemma owner_right (v : Fin N) : coverOwner (right v) = v := by simp [coverOwner,owner]
@[simp] lemma identity_left (ids : Fin N → ℕ) (v : Fin N) : coverIdentity ids (left v) = 2*ids v := by simp [coverIdentity,identity]
@[simp] lemma identity_right (ids : Fin N → ℕ) (v : Fin N) : coverIdentity ids (right v) = 2*ids v+1 := by simp [coverIdentity,identity]
@[simp] lemma side_left (v : Fin N) : coverSide (left v) = false := by simp [coverSide,side]
@[simp] lemma side_right (v : Fin N) : coverSide (right v) = true := by simp [coverSide,side]

lemma left_adj (G : SimpleGraph (Fin N)) (v : Fin N) (b : Fin (N+N)) :
    (coverGraph G).Adj (left v) b ↔ ∃ w, G.Adj v w ∧ b = right w := by
  constructor
  · intro h
    change G.bipartiteDoubleCover.Adj (indexEquiv (left v)) (indexEquiv b) at h
    rw [index_left] at h
    cases he : indexEquiv b with
    | inl w => simp only [he,SimpleGraph.bipartiteDoubleCover] at h
    | inr w =>
      refine ⟨w,?_,?_⟩
      · simpa only [he,SimpleGraph.bipartiteDoubleCover] using h
      · apply indexEquiv.injective
        rw [he,index_right]
  · rintro ⟨w,h,rfl⟩
    change G.bipartiteDoubleCover.Adj (indexEquiv (left v)) (indexEquiv (right w))
    simpa only [index_left,index_right,SimpleGraph.bipartiteDoubleCover] using h

lemma right_adj (G : SimpleGraph (Fin N)) (v : Fin N) (b : Fin (N+N)) :
    (coverGraph G).Adj (right v) b ↔ ∃ w, G.Adj v w ∧ b = left w := by
  constructor
  · intro h
    change G.bipartiteDoubleCover.Adj (indexEquiv (right v)) (indexEquiv b) at h
    rw [index_right] at h
    cases he : indexEquiv b with
    | inl w =>
      refine ⟨w,?_,?_⟩
      · simpa only [he,SimpleGraph.bipartiteDoubleCover] using h
      · apply indexEquiv.injective
        rw [he,index_left]
    | inr w => simp only [he,SimpleGraph.bipartiteDoubleCover] at h
  · rintro ⟨w,h,rfl⟩
    change G.bipartiteDoubleCover.Adj (indexEquiv (right v)) (indexEquiv (left w))
    simpa only [index_left,index_right,SimpleGraph.bipartiteDoubleCover] using h

lemma hosted_iff (a : Fin (N+N)) (v : Fin N) : coverOwner a = v ↔ a = left v ∨ a = right v := by
  constructor
  · intro h
    cases he : indexEquiv a with
    | inl w =>
      have hw : w = v := by simpa only [coverOwner,he,owner,Sum.elim_inl,id_eq] using h
      subst w
      left
      apply indexEquiv.injective
      rw [he,index_left]
    | inr w =>
      have hw : w = v := by simpa only [coverOwner,he,owner,Sum.elim_inr,id_eq] using h
      subst w
      right
      apply indexEquiv.injective
      rw [he,index_right]
  · rintro (rfl|rfl) <;> simp

def routed (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids) : Routed G (Fin (N+N)) where
  graph := coverGraph G
  owner := coverOwner
  identity := coverIdentity ids
  identity_injective := coverIdentity_injective ids hi
  route := fun a b h => (owner_adj G (indexEquiv a) (indexEquiv b) h).toWalk

lemma routed_length (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids) :
    RouteLength (routed G ids hi) 1 := by intro a b h; rfl

lemma routed_support (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (a b : Fin (N+N)) (h : (routed G ids hi).graph.Adj a b) :
    (((routed G ids hi).route a b h).support.map ids) = [ids (coverOwner a),ids (coverOwner b)] := rfl

end MatchingDoubleCover

-- Solutions/Sol_double_cover_local.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover
variable {N : ℕ}

def copy (tag : Bool) (v : Fin N) : Fin (N+N) := if tag then right v else left v

def copyName (id : ℕ) (tag : Bool) : ℕ := 2*id+if tag then 1 else 0

@[simp] lemma copy_owner (tag : Bool) (v : Fin N) : coverOwner (copy tag v) = v := by cases tag <;> simp [copy]
@[simp] lemma copy_side (tag : Bool) (v : Fin N) : coverSide (copy tag v) = tag := by cases tag <;> simp [copy]
@[simp] lemma copy_identity (ids : Fin N → ℕ) (tag : Bool) (v : Fin N) : coverIdentity ids (copy tag v) = copyName (ids v) tag := by
  cases tag <;> simp [copy,copyName]

lemma copy_adj (G : SimpleGraph (Fin N)) (tag : Bool) (v : Fin N) (b : Fin (N+N)) :
    (coverGraph G).Adj (copy tag v) b ↔ ∃ w, G.Adj v w ∧ b = copy (!tag) w := by
  cases tag <;> simp only [copy,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
  · exact left_adj G v b
  · exact right_adj G v b

lemma hosted_copy (a : Fin (N+N)) (v : Fin N) : coverOwner a = v ↔ ∃ tag, a = copy tag v := by
  rw [hosted_iff]
  constructor
  · rintro (h|h)
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · rintro ⟨tag,h⟩
    cases tag
    · exact Or.inl h
    · exact Or.inr h

def coverInput (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (a : Fin (N+N)) : Finset ℕ × Bool :=
  (neighborIDs (coverGraph G) (coverIdentity ids) a,coverSide a)

def localRoutes (id : ℕ) (neighbors : Finset ℕ) (tag : Bool) : Finset (ℕ × List ℕ) :=
  neighbors.image (fun j => (copyName j (!tag),[id,j]))

def localInput (id : ℕ) (neighbors : Finset ℕ) : Finset ℕ × RouteInput (Finset ℕ × Bool) := by
  letI : DecidableEq (Finset ℕ × Bool) := Classical.decEq _
  exact (neighbors,(univ : Finset Bool).image (fun tag =>
    (copyName id tag,(neighbors.image (fun j => copyName j (!tag)),tag),localRoutes id neighbors tag)))

lemma coverInput_copy (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (tag : Bool) (v : Fin N) :
    coverInput G ids (copy tag v) = ((neighborIDs G ids v).image (fun j => copyName j (!tag)),tag) := by
  apply Prod.ext
  · ext j
    constructor
    · intro hj
      obtain ⟨b,hb,he⟩ := mem_image.mp hj
      obtain ⟨w,hw,rfl⟩ := (copy_adj G tag v b).mp ((SimpleGraph.mem_neighborFinset (coverGraph G) _ _).mp hb)
      exact mem_image.mpr ⟨ids w,mem_image.mpr ⟨w,(SimpleGraph.mem_neighborFinset G v w).mpr hw,rfl⟩,(copy_identity ids (!tag) w).symm.trans he⟩
    · intro hj
      obtain ⟨i,hi,he⟩ := mem_image.mp hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hi
      have hAdj := (copy_adj G tag v (copy (!tag) w)).mpr ⟨w,(SimpleGraph.mem_neighborFinset G v w).mp hw,rfl⟩
      exact mem_image.mpr ⟨copy (!tag) w,(SimpleGraph.mem_neighborFinset (coverGraph G) _ _).mpr hAdj,(copy_identity ids (!tag) w).trans he⟩
  · exact copy_side tag v

lemma routes_copy (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids) (tag : Bool) (v : Fin N) :
    (univ.filter ((routed G ids hi).graph.Adj (copy tag v))).attach.image (fun b =>
      ((routed G ids hi).identity b.val,
        (((routed G ids hi).route (copy tag v) b.val (mem_filter.mp b.property).2).support.map ids))) =
      localRoutes (ids v) (neighborIDs G ids v) tag := by
  ext r
  constructor
  · intro hr
    obtain ⟨b,hb,he⟩ := mem_image.mp hr
    obtain ⟨w,hw,heq⟩ := (copy_adj G tag v b.val).mp (mem_filter.mp b.property).2
    have hp : ((routed G ids hi).identity b.val,
        (((routed G ids hi).route (copy tag v) b.val (mem_filter.mp b.property).2).support.map ids)) =
        (copyName (ids w) (!tag),[ids v,ids w]) := by
      rw [routed_support]
      change (coverIdentity ids b.val,[ids (coverOwner (copy tag v)),ids (coverOwner b.val)]) = _
      rw [heq,copy_identity,copy_owner,copy_owner]
    exact mem_image.mpr ⟨ids w,mem_image.mpr ⟨w,(SimpleGraph.mem_neighborFinset G v w).mpr hw,rfl⟩,hp.symm.trans he⟩
  · intro hr
    obtain ⟨j,hj,he⟩ := mem_image.mp hr
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
    have hAdj := (copy_adj G tag v (copy (!tag) w)).mpr ⟨w,(SimpleGraph.mem_neighborFinset G v w).mp hw,rfl⟩
    let b : {b // b ∈ univ.filter ((routed G ids hi).graph.Adj (copy tag v))} :=
      ⟨copy (!tag) w,mem_filter.mpr ⟨mem_univ _,hAdj⟩⟩
    refine mem_image.mpr ⟨b,mem_attach _ b,?_⟩
    rw [routed_support]
    change (coverIdentity ids (copy (!tag) w),[ids (coverOwner (copy tag v)),ids (coverOwner (copy (!tag) w))]) = r
    rw [copy_identity,copy_owner,copy_owner]
    exact he

lemma localInput_correct (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids) (v : Fin N) :
    localInput (ids v) (neighborIDs G ids v) = routeInput (routed G ids hi) ids (coverInput G ids) v := by
  letI : DecidableEq (Finset ℕ × Bool) := Classical.decEq _
  apply Prod.ext
  · rfl
  · ext r
    constructor
    · intro hr
      obtain ⟨tag,htag,he⟩ := mem_image.mp hr
      have ha : copy tag v ∈ univ.filter (fun a => (routed G ids hi).owner a = v) :=
        mem_filter.mpr ⟨mem_univ _,copy_owner tag v⟩
      refine mem_image.mpr ⟨copy tag v,ha,?_⟩
      rw [routes_copy]
      change (coverIdentity ids (copy tag v),coverInput G ids (copy tag v),localRoutes (ids v) (neighborIDs G ids v) tag) = r
      rw [copy_identity,coverInput_copy]
      exact he
    · intro hr
      obtain ⟨a,ha,he⟩ := mem_image.mp hr
      obtain ⟨tag,rfl⟩ := (hosted_copy a v).mp (mem_filter.mp ha).2
      refine mem_image.mpr ⟨tag,mem_univ _,?_⟩
      rw [routes_copy] at he
      change (coverIdentity ids (copy tag v),coverInput G ids (copy tag v),localRoutes (ids v) (neighborIDs G ids v) tag) = r at he
      rw [copy_identity,coverInput_copy] at he
      exact he

end MatchingDoubleCover

-- Solutions/Sol_local_transform.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalTransform

variable {K I O J P : Type}

def freeze (A : Deterministic K I O) (k : K) : Deterministic Unit I O where
  program := {
    State := A.program.State
    Msg := A.program.Msg
    rounds := fun _ => A.program.rounds k
    init := fun _ id inp _ => A.program.init k id inp (fun _ => false)
    send := A.program.send
    step := A.program.step
    out := A.program.out }
  tape_independent := by intros; rfl

lemma freeze_run (A : Deterministic K I O) (k : K) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (t : ℕ) : ∀ v,
    (freeze A k).program.run H () ids inp (fun _ _ => false) t v =
      A.program.run H k ids inp (fun _ _ => false) t v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

lemma freeze_output (A : Deterministic K I O) (k : K) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (v : V) :
    (freeze A k).program.output H () ids inp (fun _ _ => false) v =
      A.program.output H k ids inp (fun _ _ => false) v := by
  unfold SmoothedMIS.LocalAlg.output
  rw [freeze_run]
  rfl

def transform (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P) : Deterministic Unit I P where
  program := {
    State := ℕ × I × A.program.State
    Msg := A.program.Msg
    rounds := A.program.rounds
    init := fun _ id inp _ => (id,inp,A.program.init () id (pre id inp) (fun _ => false))
    send := fun st => A.program.send st.2.2
    step := fun st msgs => (st.1,st.2.1,A.program.step st.2.2 msgs)
    out := fun st => post st.1 st.2.1 (A.program.out st.2.2) }
  tape_independent := by intros; rfl

lemma transform_run (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P)
    {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (t : ℕ) : ∀ v,
    (transform A pre post).program.run H () ids inp (fun _ _ => false) t v =
      (ids v,inp v,A.program.run H () ids (fun v => pre (ids v) (inp v)) (fun _ _ => false) t v) := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

lemma transform_output (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P)
    {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (v : V) :
    (transform A pre post).program.output H () ids inp (fun _ _ => false) v =
      post (ids v) (inp v) (A.program.output H () ids (fun v => pre (ids v) (inp v)) (fun _ _ => false) v) := by
  unfold SmoothedMIS.LocalAlg.output
  rw [transform_run]
  rfl

def pointwise (f : ℕ → I → O) : Deterministic Unit I O where
  program := {
    State := O
    Msg := Unit
    rounds := fun _ => 0
    init := fun _ id inp _ => f id inp
    send := fun _ => ()
    step := fun st _ => st
    out := id }
  tape_independent := by intros; rfl

lemma local_output (f : ℕ → I → O) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (v : V) :
    (pointwise f).program.output H () ids inp (fun _ _ => false) v = f (ids v) (inp v) := rfl

end LocalTransform

-- Solutions/Sol_double_cover_simulation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover

abbrev bipartiteOracle (b : ℕ) := (lemma_3_1.choose_spec.2 (b+1)).choose
abbrev simulator (b : ℕ) :=
  (lemma_3_3.1.choose_spec.2 Bounds (Finset ℕ × Bool) (Option ℕ) (bipartiteOracle b)).choose

def coverBounds (base : Bounds) : Bounds := ⟨base.n+base.n,base.degree⟩

def coverSimulation (b : ℕ) (base : Bounds) : Deterministic Unit (Finset ℕ) (ℕ → Option (Option ℕ)) :=
  LocalTransform.transform (LocalTransform.freeze (simulator b) (coverBounds base,1))
    (fun id neighbors => localInput id neighbors) (fun _ _ out => out)

lemma coverSimulation_correct (b : ℕ) {N : ℕ} (G : SimpleGraph (Fin N)) (base : Bounds)
    (hb : boundedGraph G base.n base.degree) (ids : Fin N → ℕ) (hid : Identifiers base.n (b+1) ids) :
    ∃ M : SimpleGraph (Fin (N+N)),
      ReportsMatching (coverGraph G) (coverIdentity ids)
        (fun a => (execute (coverSimulation b base) G () ids (neighborIDs G ids) (coverOwner a) (coverIdentity ids a)).join) M ∧
      lemma_3_1.choose*(optimum (coverGraph G):ℝ) ≤ (matchingSize M:ℝ) := by
  have hB := (lemma_3_1.choose_spec.2 (b+1)).choose_spec.choose_spec
  have hBounds : boundedGraph (coverGraph G) (coverBounds base).n (coverBounds base).degree := cover_bounded G base.n base.degree hb
  have hIDs : Identifiers (coverBounds base).n ((b+1)+1) (coverIdentity ids) := cover_identifiers base.n b ids hid
  obtain ⟨M,hM,hsize⟩ := hB.2.2 (N+N) (coverGraph G) (coverBounds base) hBounds coverSide (coverGraph_bipartite G) (coverIdentity ids) hIDs
  have hS := (lemma_3_3.1.choose_spec.2 Bounds (Finset ℕ × Bool) (Option ℕ) (bipartiteOracle b)).choose_spec
  have hinp : (fun v => localInput (ids v) (neighborIDs G ids v)) = routeInput (routed G ids hid.1) ids (coverInput G ids) :=
    funext (localInput_correct G ids hid.1)
  have hout : (fun a => (execute (coverSimulation b base) G () ids (neighborIDs G ids) (coverOwner a) (coverIdentity ids a)).join) =
      execute (bipartiteOracle b) (coverGraph G) (coverBounds base) (coverIdentity ids) (coverInput G ids) := by
    funext a
    unfold execute coverSimulation
    rw [LocalTransform.transform_output,LocalTransform.freeze_output]
    change ((simulator b).program.output G (coverBounds base,1) ids (fun v => localInput (ids v) (neighborIDs G ids v))
      (fun _ _ => false) (coverOwner a) (coverIdentity ids a)).join = _
    rw [hinp]
    have hsim := hS.2 N G (Fin (N+N)) (routed G ids hid.1) 1 (routed_length G ids hid.1)
      ids hid.1 (coverBounds base) (coverInput G ids) a
    exact (congrArg Option.join hsim).trans rfl
  refine ⟨M,?_,hsize⟩
  rw [hout]
  exact hM

end MatchingDoubleCover

-- Solutions/Sol_double_cover_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingDoubleCover

lemma budget_upper (t : ℕ) (C f : ℝ) (hC : 0 ≤ C) (hf : 0 ≤ f) (ht : t ≤ budget C f) :
    (t:ℝ) ≤ C*f+1 := by
  have hh := (Nat.ceil_lt_add_one (mul_nonneg hC hf)).le
  exact (show (t:ℝ) ≤ (budget C f:ℝ) by exact_mod_cast ht).trans hh

lemma logStar_double (n : ℕ) : logStar (n+n) ≤ 3*logStar n := by
  have hX : 2 ≤ max 2 n := le_max_left _ _
  have hn : n ≤ max 2 n := le_max_right _ _
  have hpow : max 2 (n+n) ≤ (max 2 n)^2 := by apply max_le <;> nlinarith
  have h := (BlockColorProof.height_mono hpow).trans
    (BlockColorProof.height_power (max 2 n) 2 hX)
  rw [BlockColorProof.height_max_two,BlockColorProof.height_max_two] at h
  have hpos : 1 ≤ logStar n := le_max_left _ _
  omega

lemma matchingTime_double (n D : ℕ) : matchingTime (n+n) D ≤ 3*matchingTime n D := by
  have hs : (logStar (n+n):ℝ) ≤ 3*(logStar n:ℝ) := by exact_mod_cast logStar_double n
  have hterm : 0 ≤ (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by
    have hL := BipartiteRounding.degreeLog_one D
    positivity
  have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (degreeLog D))
  unfold matchingTime
  nlinarith

lemma coverSimulation_runtime (b : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ base,
    ((coverSimulation b base).program.rounds ():ℝ) ≤ C*matchingTime base.n base.degree := by
  let R := lemma_3_3.1.choose
  let B := (lemma_3_1.choose_spec.2 (b+1)).choose_spec.choose
  have hR : 0 < R := lemma_3_3.1.choose_spec.1
  have hB := (lemma_3_1.choose_spec.2 (b+1)).choose_spec.choose_spec
  have hBpos : 0 < B := hB.1
  refine ⟨2*(R:ℝ)*(3*B+1),by positivity,?_⟩
  intro base
  have ht := BipartiteRounding.time_basic_bounds base.n base.degree
  have hA : ((bipartiteOracle b).program.rounds (coverBounds base):ℝ) ≤ B*matchingTime (base.n+base.n) base.degree+1 :=
    budget_upper _ B _ hB.1.le
      (by linarith [(BipartiteRounding.time_basic_bounds (base.n+base.n) base.degree).1]) (hB.2.1 (coverBounds base))
  have hS := (lemma_3_3.1.choose_spec.2 Bounds (Finset ℕ × Bool) (Option ℕ) (bipartiteOracle b)).choose_spec.1 (coverBounds base) 1
  have hr : ((coverSimulation b base).program.rounds ():ℝ) ≤ 2*(R:ℝ)*((bipartiteOracle b).program.rounds (coverBounds base):ℝ) := by
    change ((simulator b).program.rounds (coverBounds base,1):ℝ) ≤ _
    have hsn : (simulator b).program.rounds (coverBounds base,1) ≤ 2*R*(bipartiteOracle b).program.rounds (coverBounds base) := by
      convert hS using 1 <;> ring
    exact_mod_cast hsn
  have hd := mul_le_mul_of_nonneg_left (matchingTime_double base.n base.degree) hB.1.le
  have hscaled := mul_le_mul_of_nonneg_left (show ((bipartiteOracle b).program.rounds (coverBounds base):ℝ) ≤
    (3*B+1)*matchingTime base.n base.degree by nlinarith) (show 0 ≤ 2*(R:ℝ) by positivity)
  nlinarith

end MatchingDoubleCover

-- Solutions/Sol_booster_runtime_conversion.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingBooster

lemma boost_time_generic (A C s T R U : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 1 ≤ s) (hT : 1 ≤ T)
    (hR : R ≤ 256*A*s^4*T+1) (hU : U ≤ C*s*(R+s)) :
    U ≤ C*(256*A+2)*s^5*T := by
  have hs4 : s ≤ s^4 := le_self_pow₀ hs (by decide)
  have hsT := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ s^4)
  have hinner : R+s ≤ (256*A+2)*s^4*T := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ C*s)
  nlinarith

lemma index_power_bound (epsilon : ℝ) (he : 0 < epsilon) (p : ℕ) :
    (((index epsilon+1)^p:ℕ):ℝ)^5 ≤ (4:ℝ)^(5*p)*(1+1/epsilon)^(5*p) := by
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (index epsilon:ℝ)+1) (index_bound epsilon he) (5*p)
  push_cast
  rw [←pow_mul,Nat.mul_comm p 5]
  simpa only [mul_pow] using hp

lemma runtime_conversion (A : Deterministic Bounds (Finset ℕ) (Option ℕ)) (B : Deterministic (Bounds × ℕ) (Finset ℕ) (Option ℕ))
    (p C : ℕ) (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ k, A.program.rounds k ≤ budget CA (matchingTime k.n k.degree))
    (hB : ∀ (k : Bounds) (q : ℕ), 2 ≤ q → B.program.rounds (k,q) ≤ C*(q+1)^p*
      (A.program.rounds ⟨(k.n+1)*(q+1)^p,(k.degree+1)*(q+1)^p⟩+(q+1)^p))
    (k : Bounds) (epsilon : ℝ) (he : 0 < epsilon) :
    (B.program.rounds (k,index epsilon):ℝ) ≤
      ((C:ℝ)*(256*CA+2)*4^(5*p))*((1+1/epsilon)^(5*p)*matchingTime k.n k.degree) := by
  let q := index epsilon
  let s := (q+1)^p
  let k' : Bounds := ⟨(k.n+1)*s,(k.degree+1)*s⟩
  have hs : 1 ≤ s := one_le_pow₀ (by dsimp [q];omega)
  have hs' : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hT := (BipartiteRounding.time_basic_bounds k.n k.degree).1
  have hT' := (BipartiteRounding.time_basic_bounds k'.n k'.degree).1
  have hAi := MatchingDoubleCover.budget_upper _ CA _ hCA.le (by linarith : 0 ≤ matchingTime k'.n k'.degree) (hA k')
  have hinf := matchingTime_product k.n k.degree s hs
  have hscaled := mul_le_mul_of_nonneg_left hinf hCA.le
  have hR : (A.program.rounds k':ℝ) ≤ 256*CA*(s:ℝ)^4*matchingTime k.n k.degree+1 := by nlinarith
  have hUB : (B.program.rounds (k,q):ℝ) ≤ (C:ℝ)*(s:ℝ)*((A.program.rounds k':ℝ)+(s:ℝ)) := by
    have hh := hB k q (index_two epsilon)
    change B.program.rounds (k,q) ≤ C*s*(A.program.rounds k'+s) at hh
    exact_mod_cast hh
  have ht := boost_time_generic CA (C:ℝ) (s:ℝ) (matchingTime k.n k.degree) _ _ hCA.le (Nat.cast_nonneg _) hs' hT hR hUB
  have hp : (s:ℝ)^5 ≤ (4:ℝ)^(5*p)*(1+1/epsilon)^(5*p) := index_power_bound epsilon he p
  have hcoef : 0 ≤ (C:ℝ)*(256*CA+2)*matchingTime k.n k.degree := by positivity
  have hfinal := mul_le_mul_of_nonneg_left hp hcoef
  nlinarith

end MatchingBooster

-- Solutions/Sol_local_family.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalFamily
section Family
variable {K I O : Type} (F : K → Deterministic Unit I O)

abbrev FamilyState := Σ k : K, (F k).program.State
abbrev FamilyMessage := Σ k : K, (F k).program.Msg

def unpack (k : K) (msg : FamilyMessage F) : Option (F k).program.Msg :=
  if h : msg.1 = k then some (h ▸ msg.2) else none

lemma unpack_same (k : K) (msg : (F k).program.Msg) : unpack F k ⟨k,msg⟩ = some msg := by
  unfold unpack
  rw [dif_pos rfl]

def select : Deterministic K I O where
  program := {
    State := FamilyState F
    Msg := FamilyMessage F
    rounds := fun k => (F k).program.rounds ()
    init := fun k id inp _ => ⟨k,(F k).program.init () id inp (fun _ => false)⟩
    send := fun st => ⟨st.1,(F st.1).program.send st.2⟩
    step := fun st msgs => ⟨st.1,(F st.1).program.step st.2 (msgs.filterMap (unpack F st.1))⟩
    out := fun st => (F st.1).program.out st.2 }
  tape_independent := by intros; rfl

lemma select_run {V : Type} [Fintype V] (H : SimpleGraph V) (k : K) (ids : V → ℕ)
    (inp : V → I) (t : ℕ) : ∀ v,
    (select F).program.run H k ids inp (fun _ _ => false) t v =
      ⟨k,(F k).program.run H () ids inp (fun _ _ => false) t v⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    change (⟨k,(F k).program.step ((F k).program.run H () ids inp (fun _ _ => false) t v)
      (((univ.filter (H.Adj v)).val.map (fun w =>
        (⟨k,(F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t w)⟩ : FamilyMessage F))).filterMap (unpack F k))⟩ : FamilyState F) = _
    rw [Multiset.filterMap_map]
    simp only [Function.comp_def,unpack_same]
    rw [show (fun x => some ((F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t x))) =
      some ∘ (fun x => (F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t x)) from rfl,
      ←Multiset.filterMap_map,Multiset.filterMap_some]
    rfl

lemma select_output {V : Type} [Fintype V] (H : SimpleGraph V) (k : K) (ids : V → ℕ)
    (inp : V → I) (v : V) :
    (select F).program.output H k ids inp (fun _ _ => false) v =
      (F k).program.output H () ids inp (fun _ _ => false) v := by
  unfold SmoothedMIS.LocalAlg.output
  change (select F).program.out ((select F).program.run H k ids inp (fun _ _ => false) ((F k).program.rounds ()) v) = _
  rw [select_run]
  rfl

end Family
end LocalFamily

-- Solutions/Sol_main_reduction.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingBooster

def accuracyProgram (B : Deterministic (Bounds × ℕ) (Finset ℕ) (Option ℕ)) : Deterministic Accuracy (Finset ℕ) (Option ℕ) :=
  LocalFamily.select (fun k : Accuracy => LocalTransform.freeze B (k.toBounds,index k.epsilon))

lemma accuracyProgram_output (B : Deterministic (Bounds × ℕ) (Finset ℕ) (Option ℕ))
    {N : ℕ} (G : SimpleGraph (Fin N)) (k : Accuracy) (ids : Fin N → ℕ) (inp : Fin N → Finset ℕ) :
    execute (accuracyProgram B) G k ids inp = execute B G (k.toBounds,index k.epsilon) ids inp := by
  funext v
  unfold execute accuracyProgram
  rw [LocalFamily.select_output,LocalTransform.freeze_output]

end MatchingBooster

open MatchingBooster

theorem solution :
    ∀ b : ℕ, ∃ (A : Deterministic Accuracy (Finset ℕ) (Option ℕ)) (C : ℝ) (d : ℕ),
      0 < C ∧
      (∀ k : Accuracy, 0 < k.epsilon →
        A.program.rounds k ≤ budget C ((1 + 1 / k.epsilon) ^ d * matchingTime k.n k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Accuracy),
        0 < k.epsilon → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ M : SimpleGraph (Fin N),
            ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M ∧
            (optimum G : ℝ) ≤ (1 + k.epsilon) * (matchingSize M : ℝ) := by
  obtain ⟨c0,hc0,hgeneral⟩ := general_graph_constant_approximation
  let c := min c0 1
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hc1 : c ≤ 1 := min_le_right _ _
  obtain ⟨p,C,hp,hC,hframework⟩ := fmu_local_booster c hc hc1
  intro b
  obtain ⟨A,CA,hCA,hTA,hA⟩ := hgeneral (b+3)
  have hOracle : ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds),
      boundedGraph G k.n k.degree → ∀ ids : Fin N → ℕ, Identifiers k.n (b+4) ids →
        ∃ M : SimpleGraph (Fin N), ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M ∧
          c*(optimum G:ℝ) ≤ (matchingSize M:ℝ) := by
    intro N G k hb ids hid
    have hid' : Identifiers k.n ((b+3)+1) ids := by simpa only [Nat.add_assoc] using hid
    obtain ⟨M,hM,hs⟩ := hA N G k hb ids hid'
    refine ⟨M,hM,?_⟩
    exact (mul_le_mul_of_nonneg_right (min_le_left c0 1) (Nat.cast_nonneg _)).trans hs
  obtain ⟨B,hTB,hB⟩ := hframework b A hOracle
  let K : ℝ := (C:ℝ)*(256*CA+2)*4^(5*p)
  have hK : 0 < K := by
    have hC' : (0:ℝ) < C := by exact_mod_cast hC
    dsimp only [K]
    positivity
  refine ⟨accuracyProgram B,K,5*p,hK,?_,?_⟩
  · intro k he
    have ht := runtime_conversion A B p C CA hCA hTA hTB k.toBounds k.epsilon he
    change ((accuracyProgram B).program.rounds k:ℝ) ≤ K*((1+1/k.epsilon)^(5*p)*matchingTime k.n k.degree) at ht
    change (accuracyProgram B).program.rounds k ≤ ⌈K*((1+1/k.epsilon)^(5*p)*matchingTime k.n k.degree)⌉₊
    exact_mod_cast ht.trans (Nat.le_ceil (K*((1+1/k.epsilon)^(5*p)*matchingTime k.n k.degree)))
  · intro N G k he hb ids hid
    obtain ⟨M,hM,hs⟩ := hB N G k.toBounds (index k.epsilon) (index_two k.epsilon) hb ids hid
    refine ⟨M,?_,?_⟩
    · rw [accuracyProgram_output]
      exact hM
    · have hacc := index_accuracy k.epsilon he
      have hh := mul_le_mul_of_nonneg_right hacc (Nat.cast_nonneg (matchingSize M))
      nlinarith
