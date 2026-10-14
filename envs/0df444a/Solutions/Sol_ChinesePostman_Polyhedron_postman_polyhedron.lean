-- Prove2me | solution 1 for ChinesePostman.Polyhedron.postman_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T07:14:34.357027+00:00
-- url     : https://prove2.me/submissions/ebb42343-51d5-4c90-813b-4c75798dbedc

-- Complete checked reconstruction of the native Chinese-postman parity polyhedron theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_ChinesePostman_Polyhedron_Setting
import Mathlib


-- Begin Canonical

open Set Finset
namespace ChinesePostman.Polyhedron.Proof
end ChinesePostman.Polyhedron.Proof
-- End Canonical

-- Begin Generic

namespace ChinesePostman.Polyhedron.Proof

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def CutPoly (G : Graph V E) (T : Finset V) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset V, Odd (S ∩ T).card → 1 ≤ cutSum G x S}

def DegreePoly (G : Graph V E) (T : Finset V) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ v ∈ T, 1 ≤ incidentSum G x v}

def IsJoin (G : Graph V E) (T : Finset V) (J : Finset E) : Prop :=
  ∀ v, Odd (J.filter (fun e => v ∈ G.ends e)).card ↔ v ∈ T

def joinVector (J : Finset E) : E → ℝ := fun e => if e ∈ J then 1 else 0

def joinPoints (G : Graph V E) (T : Finset V) : Set (E → ℝ) :=
  {x | ∃ J : Finset E, IsJoin G T J ∧ x = joinVector J}

def dominant (G : Graph V E) (T : Finset V) : Set (E → ℝ) :=
  {x | ∃ y ∈ convexHull ℝ (joinPoints G T), ∀ e, y e ≤ x e}

omit [Fintype E] in
lemma joinVector_nonneg (J : Finset E) (e : E) : 0 ≤ joinVector J e := by
  unfold joinVector
  split_ifs <;> norm_num

omit [Fintype V] in
lemma joinPoints_finite (G : Graph V E) (T : Finset V) : (joinPoints G T).Finite := by
  apply (Set.toFinite (Set.range (@joinVector E _))).subset
  rintro x ⟨J, _, rfl⟩
  exact ⟨J, rfl⟩

end ChinesePostman.Polyhedron.Proof
-- End Generic

-- Begin PolyBody

open Set

namespace ChinesePostman.Polyhedron.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

def polyBody (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}

lemma polyBody_convex (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (polyBody a b) := by
  intro x hx y hy s t hs ht hsum i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    s*a i x+t*a i y ≤ s*b i+t*b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul,hsum,one_mul]

end ChinesePostman.Polyhedron.Proof
-- End PolyBody

-- Begin FiniteSlack

open Set Filter
open scoped Topology

namespace ChinesePostman.Polyhedron.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v d : E}

lemma feasible_direction_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∀ᶠ t : ℝ in 𝓝 0, 0≤t → v+t • d ∈ polyBody a b := by
  have hh : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0≤t → a i (v+t • d)≤b i := by
    intro i
    by_cases hi : a i v=b i
    · exact Eventually.of_forall fun t ht=>by
        simp only [map_add,map_smul,smul_eq_mul,hi]
        exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht (hd i hi))
    · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
      have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
        have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
        simpa only [zero_mul,add_zero] using hcont.tendsto 0
      filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
      intro _
      simpa only [map_add,map_smul,smul_eq_mul] using ht.le
  filter_upwards [eventually_all.mpr hh] with t ht hpos i
  exact ht i hpos

lemma feasible_direction_step (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∃ t : ℝ, 0<t ∧ v+t • d ∈ polyBody a b := by
  obtain ⟨t,ht,hf⟩ := (feasible_direction_nhds hv hd).exists_gt
  exact ⟨t,ht,hf ht.le⟩

lemma feasible_kernel_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d=0) :
    ∀ᶠ t : ℝ in 𝓝 0, v+t • d ∈ polyBody a b := by
  apply eventually_all.mpr
  intro i
  by_cases hi : a i v=b i
  · exact Eventually.of_forall fun t=>by simp [map_add,map_smul,hi,hd i hi]
  · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
    have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
      have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
      simpa only [zero_mul,add_zero] using hcont.tendsto 0
    filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
    simpa only [map_add,map_smul,smul_eq_mul] using ht.le

end ChinesePostman.Polyhedron.Proof
-- End FiniteSlack

-- Begin VertexKernel

open Set Filter
open scoped Topology

namespace ChinesePostman.Polyhedron.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v : E}

lemma vertex_kernel_zero (hv : v ∈ (polyBody a b).extremePoints ℝ) {d : E}
    (hd : ∀ i, a i v=b i → a i d=0) : d=0 := by
  have hp := feasible_kernel_nhds hv.1 hd
  have hm := feasible_kernel_nhds hv.1 (d := -d) (fun i hi=>by simp [hd i hi])
  obtain ⟨t,ht,hplus,hminus⟩ := (hp.and hm).exists_gt
  have he : v+t • d=v := hv.2 hplus hminus (by
    simpa only [smul_neg,←sub_eq_add_neg] using mem_openSegment_add_sub (𝕜:=ℝ) v (t • d))
  exact (smul_eq_zero.mp (add_eq_left.mp he)).resolve_left ht.ne'

omit [Fintype ι] in
lemma mem_extremePoints_of_kernel_zero (hv : v ∈ polyBody a b)
    (hk : ∀ d : E, (∀ i, a i v=b i → a i d=0) → d=0) :
    v ∈ (polyBody a b).extremePoints ℝ := by
  refine ⟨hv,?_⟩
  intro x hx y hy hseg
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  apply sub_eq_zero.mp
  apply hk
  intro i hi
  have he' := congrArg (a i) he
  simp only [map_add,map_smul,smul_eq_mul,hi] at he'
  have hx' := hx i
  have hy' := hy i
  have hex : a i x=b i := by
    have hm := mul_le_mul_of_nonneg_left hy' ht.le
    have hsum : s*b i+t*b i=b i := by rw [←add_mul,hst,one_mul]
    apply le_antisymm hx'
    apply (mul_le_mul_iff_right₀ hs).mp
    linarith
  simp only [map_sub,hex,hi,sub_self]

lemma vertex_iff_kernel_zero (hv : v ∈ polyBody a b) :
    v ∈ (polyBody a b).extremePoints ℝ ↔
      ∀ d : E, (∀ i, a i v=b i → a i d=0) → d=0 :=
  ⟨fun h _ hd=>vertex_kernel_zero h hd,mem_extremePoints_of_kernel_zero hv⟩

end ChinesePostman.Polyhedron.Proof
-- End VertexKernel

-- Begin IncidenceBasic

open Set
namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def incidentLinear (G : Graph V E) (v : V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => incidentSum G x v
  map_add' x y := by
    classical
    simp [incidentSum, Finset.sum_add_distrib]
  map_smul' t x := by
    classical
    simp [incidentSum, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
@[simp] lemma incidentLinear_apply (G : Graph V E) (v : V) (x : E → ℝ) :
    incidentLinear G v x = incidentSum G x v := rfl

omit [Fintype V] [DecidableEq E] in
lemma incidentSum_nonneg (G : Graph V E) {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) (v : V) :
    0 ≤ incidentSum G x v := by
  classical
  exact Finset.sum_nonneg (fun e _ => hx e)

omit [Fintype V] [DecidableEq E] in
lemma coordinate_le_incident (G : Graph V E) {x : E → ℝ} (hx : ∀ e, 0 ≤ x e)
    {e : E} {v : V} (he : v ∈ G.ends e) : x e ≤ incidentSum G x v := by
  classical
  exact Finset.single_le_sum (fun a _ => hx a) (by simp [he])

omit [Fintype V] in
lemma incident_single (G : Graph V E) (v : V) (e : E) (t : ℝ) :
    incidentSum G (Pi.single e t) v = if v ∈ G.ends e then t else 0 := by
  classical
  simp [incidentSum, Pi.single_apply, Finset.sum_ite_eq']

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma graph_ends_exists (G : Graph V E) (e : E) :
    ∃ u v, u ≠ v ∧ G.ends e = s(u,v) := by
  have h := G.loopless e
  generalize hh : G.ends e = a at *
  induction a using Sym2.inductionOn with
  | _ u v => exact ⟨u,v,by simpa using h,rfl⟩

noncomputable def degreeRows (G : Graph V E) (T : Finset V) :
    E ⊕ {v // v ∈ T} → (E → ℝ) →ₗ[ℝ] ℝ
  | Sum.inl e => -(LinearMap.proj e)
  | Sum.inr v => -(incidentLinear G v)

def degreeRhs (T : Finset V) : E ⊕ {v // v ∈ T} → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

omit [Fintype V] [DecidableEq E] in
lemma degreePoly_eq (G : Graph V E) (T : Finset V) :
    DegreePoly G T = polyBody (degreeRows G T) (degreeRhs T) := by
  ext x
  constructor
  · rintro ⟨hx,hv⟩ (e|v)
    · simpa [degreeRows,degreeRhs] using hx e
    · simpa [degreeRows,degreeRhs] using hv v v.property
  · intro h
    refine ⟨fun e => ?_,fun v hv => ?_⟩
    · simpa [degreeRows,degreeRhs] using h (Sum.inl e)
    · simpa [degreeRows,degreeRhs] using h (Sum.inr ⟨v,hv⟩)

omit [Fintype V] [DecidableEq E] in
lemma degree_vertex_kernel (G : Graph V E) (T : Finset V) {x d : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ)
    (hz : ∀e, x e = 0 → d e = 0)
    (ht : ∀v∈T, incidentSum G x v = 1 → incidentSum G d v = 0) : d = 0 := by
  rw [degreePoly_eq] at hx
  apply vertex_kernel_zero hx
  rintro (e|v) h
  · have he : x e = 0 := by simpa [degreeRows,degreeRhs] using h
    simp [degreeRows,hz e he]
  · have he : incidentSum G x v = 1 := by
      simpa [degreeRows,degreeRhs] using h
    simp [degreeRows,ht v v.property he]

end ChinesePostman.Polyhedron.Proof
-- End IncidenceBasic

-- Begin CutBasic

namespace ChinesePostman.Polyhedron.Proof

variable {V E : Type} [DecidableEq V]

omit [DecidableEq V] in
lemma meets_pair (G : Graph V E) (e : E) {u v : V} (he : G.ends e = s(u,v))
    (S : Finset V) : Meets G e S ↔ (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    rw [he, Sym2.eq_iff] at hab
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨u,v,he,hu,hv⟩
    · exact ⟨v,u,he.trans (Sym2.eq_swap),hv,hu⟩

omit [DecidableEq V] in
lemma meets_singleton (G : Graph V E) (e : E) (v : V) :
    Meets G e {v} ↔ v ∈ G.ends e := by
  obtain ⟨a,b,hab,he⟩ := graph_ends_exists G e
  rw [meets_pair G e he, he]
  simp only [Finset.mem_singleton, Sym2.mem_iff]
  aesop

omit [DecidableEq V] in
lemma meets_empty (G : Graph V E) (e : E) : ¬Meets G e ∅ := by
  rintro ⟨u,v,_,hu,_⟩
  simp at hu

omit [DecidableEq V] in
lemma meets_univ [Fintype V] (G : Graph V E) (e : E) : ¬Meets G e Finset.univ := by
  rintro ⟨u,v,_,_,hv⟩
  exact hv (Finset.mem_univ _)

lemma meets_compl [Fintype V] (G : Graph V E) (e : E) (S : Finset V) :
    Meets G e Sᶜ ↔ Meets G e S := by
  obtain ⟨a,b,_,he⟩ := graph_ends_exists G e
  rw [meets_pair G e he, meets_pair G e he]
  simp only [Finset.mem_compl, not_not]
  tauto

variable [Fintype E]

lemma cutSum_singleton {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α) (v : V) :
    cutSum G x {v} = incidentSum G x v := by
  simp only [cutSum, incidentSum, meets_singleton]

omit [DecidableEq V] in
lemma cutSum_empty {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α) :
    cutSum G x ∅ = 0 := by
  simp [cutSum, meets_empty]

omit [DecidableEq V] in
lemma cutSum_univ [Fintype V] {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α) :
    cutSum G x Finset.univ = 0 := by
  simp [cutSum, meets_univ]

lemma cutSum_compl [Fintype V] {α : Type} [AddCommMonoid α] (G : Graph V E)
    (x : E → α) (S : Finset V) : cutSum G x Sᶜ = cutSum G x S := by
  unfold cutSum
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact meets_compl G e S

lemma cutPoly_degree (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ CutPoly G T) : x ∈ DegreePoly G T := by
  refine ⟨hx.1, fun v hv => ?_⟩
  have h := hx.2 {v} (by simp [hv])
  rwa [cutSum_singleton] at h

lemma cutPoly_total_even [Fintype V] (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ CutPoly G T) : Even T.card := by
  by_contra hn
  have ho : Odd T.card := Nat.not_even_iff_odd.mp hn
  have h := hx.2 Finset.univ (by simpa using ho)
  rw [cutSum_univ] at h
  norm_num at h

end ChinesePostman.Polyhedron.Proof
-- End CutBasic

-- Begin ParityFibers

namespace ChinesePostman.Polyhedron.Proof

variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma sum_fiber_card (T : Finset V) (A : Finset W) (f : V → W) :
    (∑ w ∈ A, (T.filter (fun v => f v = w)).card) = (T.filter (fun v => f v ∈ A)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp

variable [Fintype W]

def pushParity (T : Finset V) (f : V → W) : Finset W :=
  Finset.univ.filter (fun w => Odd (T.filter (fun v => f v = w)).card)

omit [DecidableEq V] in
lemma odd_fiber_preimage (T : Finset V) (A : Finset W) (f : V → W) :
    Odd (T.filter (fun v => f v ∈ A)).card ↔ Odd (A ∩ pushParity T f).card := by
  rw [← sum_fiber_card T A f, Finset.odd_sum_iff_odd_card_odd]
  have he : A.filter (fun w => Odd (T.filter (fun v => f v = w)).card) = A ∩ pushParity T f := by
    ext w
    simp [pushParity]
  rw [he]

end ChinesePostman.Polyhedron.Proof
-- End ParityFibers

-- Begin QuotientGraph

namespace ChinesePostman.Polyhedron.Proof

variable {V E W : Type}

def Survives (G : Graph V E) (f : V → W) (e : E) : Prop :=
  ¬ ((G.ends e).map f).IsDiag

noncomputable instance quotientEdgesFintype [Fintype E] (G : Graph V E) (f : V → W) :
    Fintype {e // Survives G f e} := Fintype.ofFinite _

noncomputable def quotientGraph (G : Graph V E) (f : V → W) :
    Graph W {e // Survives G f e} where
  ends e := (G.ends e.val).map f
  loopless e := e.property

variable [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma quotient_meets [Fintype V] (G : Graph V E) (f : V → W)
    (e : {e // Survives G f e}) (A : Finset W) :
    Meets (quotientGraph G f) e A ↔ Meets G e.val (Finset.univ.filter (fun v => f v ∈ A)) := by
  obtain ⟨u,v,_,he⟩ := graph_ends_exists G e.val
  have he' : (quotientGraph G f).ends e = s(f u,f v) := by
    change (G.ends e.val).map f = _
    rw [he, Sym2.map_mk]
  rw [meets_pair _ _ he', meets_pair _ _ he]
  simp

omit [DecidableEq V] in
lemma survives_of_meets_preimage [Fintype V] (G : Graph V E) (f : V → W) (e : E)
    (A : Finset W) (h : Meets G e (Finset.univ.filter (fun v => f v ∈ A))) :
    Survives G f e := by
  obtain ⟨u,v,he,hu,hv⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  unfold Survives
  rw [he, Sym2.map_mk]
  simpa using (show f u ≠ f v from fun heq => hv (heq ▸ hu))

end ChinesePostman.Polyhedron.Proof
-- End QuotientGraph

-- Begin QuotientCuts

namespace ChinesePostman.Polyhedron.Proof
variable {V E W : Type} [Fintype V] [Fintype E] [Fintype W]
  [DecidableEq V] [DecidableEq E] [DecidableEq W]

omit [Fintype W] [DecidableEq V] [DecidableEq E] in
lemma quotient_cutSum {α : Type} [AddCommMonoid α] (G : Graph V E) (f : V → W)
    (x : E → α) (A : Finset W) :
    cutSum (quotientGraph G f) (fun e => x e.val) A =
      cutSum G x (Finset.univ.filter (fun v => f v ∈ A)) := by
  classical
  unfold cutSum
  apply Finset.sum_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact (quotient_meets G f e A).mp he
  · intro e _ e' _ h
    exact Subtype.ext h
  · intro e he
    have hm : Meets G e (Finset.univ.filter (fun v => f v ∈ A)) := (Finset.mem_filter.mp he).2
    refine ⟨⟨e,survives_of_meets_preimage G f e A hm⟩,?_,rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (quotient_meets G f _ A).mpr hm
  · intro e _
    rfl

omit [DecidableEq E] in
lemma quotient_cutPoly (G : Graph V E) (T : Finset V) (f : V → W) {x : E → ℝ}
    (hx : x ∈ CutPoly G T) :
    (fun e => x e.val) ∈ CutPoly (quotientGraph G f) (pushParity T f) := by
  classical
  refine ⟨fun e => hx.1 e.val, fun A hA => ?_⟩
  rw [quotient_cutSum]
  apply hx.2
  have ho := (odd_fiber_preimage T A f).mpr hA
  have he : (Finset.univ.filter (fun v => f v ∈ A)) ∩ T = T.filter (fun v => f v ∈ A) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rwa [he]

end ChinesePostman.Polyhedron.Proof
-- End QuotientCuts

-- Begin Contraction

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def collapseVertex (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

omit [Fintype V] in
lemma collapse_none (S : Finset V) (v : V) : collapseVertex S v = none ↔ v ∉ S := by
  unfold collapseVertex
  split_ifs <;> simp_all

omit [Fintype V] in
lemma collapse_some (S : Finset V) (v : V) (u : {v // v ∈ S}) :
    collapseVertex S v = some u ↔ v = u.val := by
  unfold collapseVertex
  split_ifs with h
  · simp only [Option.some.injEq, Subtype.ext_iff]
  · simp only [false_iff]
    intro he
    exact h (he ▸ u.property)

lemma collapse_card_lt (S : Finset V) (hS : 2 ≤ Sᶜ.card) :
    Fintype.card (Option {v // v ∈ S}) < Fintype.card V := by
  rw [Fintype.card_option, Fintype.card_coe]
  have h := Finset.card_add_card_compl S
  omega

omit [Fintype V] [DecidableEq E] [Fintype E] in
lemma survives_collapse (G : Graph V E) (S : Finset V) (e : E) :
    Survives G (collapseVertex S) e ↔ ∃ v ∈ G.ends e, v ∈ S := by
  obtain ⟨u,v,huv,he⟩ := graph_ends_exists G e
  simp only [Survives, he, Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mem_iff]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [collapseVertex, hu, hv, huv]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma pushParity_collapse_some (S T : Finset V) (u : {v // v ∈ S}) :
    some u ∈ pushParity T (collapseVertex S) ↔ u.val ∈ T := by
  simp only [pushParity, Finset.mem_filter, Finset.mem_univ, true_and, collapse_some]
  by_cases h : u.val ∈ T
  · simp [Finset.filter_eq', h]
  · simp [Finset.filter_eq', h]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma pushParity_collapse_none (S T : Finset V) :
    none ∈ pushParity T (collapseVertex S) ↔ Odd (T \ S).card := by
  simp only [pushParity, Finset.mem_filter, Finset.mem_univ, true_and, collapse_none]
  have he : T.filter (fun x => x ∉ S) = T \ S := by
    ext v
    simp
  rw [he]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma pushParity_collapse_none_of_odd (S T : Finset V)
    (hS : Odd (S ∩ T).card) (hT : Even T.card) :
    none ∈ pushParity T (collapseVertex S) := by
  rw [pushParity_collapse_none, Nat.odd_iff]
  have ho := Nat.odd_iff.mp hS
  have he := Nat.even_iff.mp hT
  have hc := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hc
  omega

end ChinesePostman.Polyhedron.Proof
-- End Contraction

-- Begin CrossingBasic

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def cutEdges (G : Graph V E) (S : Finset V) : Finset E :=
  by classical exact Finset.univ.filter (fun e => Meets G e S)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma mem_cutEdges (G : Graph V E) (S : Finset V) (e : E) :
    e ∈ cutEdges G S ↔ Meets G e S := by simp [cutEdges]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma meets_survives_collapse (G : Graph V E) (S : Finset V) {e : E}
    (he : Meets G e S) : Survives G (collapseVertex S) e := by
  rcases he with ⟨u,v,h,hu,_⟩
  rw [survives_collapse]
  exact ⟨u,by simp [h],hu⟩

omit [Fintype E] [DecidableEq E] in
lemma survives_both_iff_meets (G : Graph V E) (S : Finset V) (e : E) :
    Survives G (collapseVertex S) e ∧ Survives G (collapseVertex Sᶜ) e ↔ Meets G e S := by
  obtain ⟨u,v,huv,he⟩ := graph_ends_exists G e
  rw [survives_collapse,survives_collapse,meets_pair G e he]
  simp only [he,Sym2.mem_iff,Finset.mem_compl]
  aesop

omit [Fintype E] [DecidableEq E] in
lemma survives_one (G : Graph V E) (S : Finset V) (e : E) :
    Survives G (collapseVertex S) e ∨ Survives G (collapseVertex Sᶜ) e := by
  obtain ⟨u,v,_,he⟩ := graph_ends_exists G e
  by_cases hu : u ∈ S
  · exact Or.inl ((survives_collapse G S e).mpr ⟨u,by simp [he],hu⟩)
  · exact Or.inr ((survives_collapse G Sᶜ e).mpr ⟨u,by simp [he],by simpa using hu⟩)

omit [Fintype E] [DecidableEq E] in
lemma fresh_incident_iff (G : Graph V E) (S : Finset V)
    (e : {e // Survives G (collapseVertex S) e}) :
    none ∈ (quotientGraph G (collapseVertex S)).ends e ↔ Meets G e.val S := by
  rw [← meets_singleton]
  rw [quotient_meets]
  have he : Finset.univ.filter (fun v => collapseVertex S v ∈ ({none} : Finset (Option {v // v ∈ S}))) = Sᶜ := by
    ext v
    simp [collapse_none]
  rw [he,meets_compl]

omit [DecidableEq E] in
lemma fresh_cutSum (G : Graph V E) (S : Finset V) (x : E → ℝ) :
    incidentSum (quotientGraph G (collapseVertex S)) (fun e => x e.val) none = cutSum G x S := by
  rw [← cutSum_singleton,quotient_cutSum]
  have he : Finset.univ.filter (fun v => collapseVertex S v ∈ ({none} : Finset (Option {v // v ∈ S}))) = Sᶜ := by
    ext v
    simp [collapse_none]
  rw [he,cutSum_compl]

end ChinesePostman.Polyhedron.Proof
-- End CrossingBasic

-- Begin CutCounting

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [DecidableEq V] [Fintype E]

lemma sum_endpoint_weights {α : Type} [AddCommMonoid α] (S : Finset V)
    {u v : V} (huv : u ≠ v) (a : α) :
    (∑ w ∈ S, if w ∈ s(u,v) then a else 0) =
      (if u ∈ S then a else 0) + (if v ∈ S then a else 0) := by
  have h (w : V) : (if w ∈ s(u,v) then a else 0) =
      (if w = u then a else 0) + (if w = v then a else 0) := by
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp_all [Sym2.mem_iff]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp

def Inside (G : Graph V E) (e : E) (S : Finset V) : Prop := ∀ v ∈ G.ends e, v ∈ S

noncomputable instance insideDecidable (G : Graph V E) (e : E) (S : Finset V) :
    Decidable (Inside G e S) := Classical.propDecidable _

lemma incident_cut_count {α : Type} [AddCommMonoid α] (G : Graph V E)
    (x : E → α) (S : Finset V) :
    (∑ v ∈ S, incidentSum G x v) = cutSum G x S +
      2 • (∑ e ∈ Finset.univ.filter (fun e => Inside G e S), x e) := by
  classical
  simp only [incidentSum, cutSum, Finset.sum_filter, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨u,v,huv,he⟩ := graph_ends_exists G e
  have hi : Inside G e S ↔ u ∈ S ∧ v ∈ S := by
    simp [Inside, he, Sym2.mem_iff]
  rw [he, sum_endpoint_weights S huv]
  have hm := meets_pair G e he S
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [hm, hi, hu, hv, two_nsmul]

end ChinesePostman.Polyhedron.Proof
-- End CutCounting

-- Begin PositiveCost

namespace ChinesePostman.Polyhedron.Proof

variable {E : Type} [Fintype E]

noncomputable def linearCost (c : E → ℝ) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ e, c e * x e
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]; congr 1; ext e; ring

lemma linearCost_apply (c x : E → ℝ) : linearCost c x = ∑ e, c e * x e := rfl

lemma positive_sublevel_compact {P : Set (E → ℝ)} (hP : IsClosed P)
    (hpos : ∀ x ∈ P, ∀ e, 0 ≤ x e) (c : E → ℝ) (hc : ∀ e, 0 < c e) (a : ℝ) :
    IsCompact {x ∈ P | linearCost c x ≤ a} := by
  have hclosed : IsClosed {x ∈ P | linearCost c x ≤ a} :=
    hP.inter (isClosed_le (linearCost c).continuous_of_finiteDimensional continuous_const)
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) (fun e => a / c e))).of_isClosed_subset hclosed
  intro x hx
  refine ⟨hpos x hx.1, fun e => ?_⟩
  apply (le_div_iff₀ (hc e)).mpr
  have hterm : c e * x e ≤ linearCost c x :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hc i).le (hpos x hx.1 i)) (Finset.mem_univ e)
  simpa only [mul_comm] using hterm.trans hx.2

lemma exists_extreme_min_positive {P : Set (E → ℝ)} (hP : IsClosed P)
    (hpos : ∀ x ∈ P, ∀ e, 0 ≤ x e) (hne : P.Nonempty)
    (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    ∃ z ∈ P.extremePoints ℝ, ∀ x ∈ P, linearCost c z ≤ linearCost c x := by
  obtain ⟨x₀, hx₀⟩ := hne
  let K := {x ∈ P | linearCost c x ≤ linearCost c x₀}
  have hK : IsCompact K := positive_sublevel_compact hP hpos c hc _
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨x₀, hx₀, le_rfl⟩
    (linearCost c).continuous_of_finiteDimensional.continuousOn
  have hglobal : ∀ x ∈ P, linearCost c z ≤ linearCost c x := by
    intro x hx
    by_cases hh : linearCost c x ≤ linearCost c x₀
    · exact hmin ⟨hx, hh⟩
    · exact hz.2.trans (le_of_not_ge hh)
  let F := {x ∈ P | ∀ y ∈ P, linearCost c x ≤ linearCost c y}
  have hF : F.Nonempty := ⟨z, hz.1, hglobal⟩
  have hex : IsExposed ℝ P F := by
    intro _
    refine ⟨⟨-linearCost c, (-linearCost c).continuous_of_finiteDimensional⟩, ?_⟩
    ext x
    change (x ∈ P ∧ ∀ y ∈ P, linearCost c x ≤ linearCost c y) ↔
      (x ∈ P ∧ ∀ y ∈ P, -(linearCost c y) ≤ -(linearCost c x))
    simp only [neg_le_neg_iff]
  have hcomp : IsCompact F := hK.of_isClosed_subset (hex.isClosed hP)
    (fun x hx => ⟨hx.1, hx.2 x₀ hx₀⟩)
  obtain ⟨w, hw⟩ := hcomp.extremePoints_nonempty hF
  exact ⟨w, hex.isExtreme.extremePoints_subset_extremePoints hw, hw.1.2⟩

end ChinesePostman.Polyhedron.Proof
-- End PositiveCost

-- Begin PositiveGeneration

namespace ChinesePostman.Polyhedron.Proof

variable {E : Type} [Fintype E] [DecidableEq E]

lemma linear_eq_cost (f : (E → ℝ) →ₗ[ℝ] ℝ) (x : E → ℝ) :
    f x = linearCost (fun e => f (Pi.single e 1)) x := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  have he : Pi.single e (x e) = x e • (Pi.single e 1 : E → ℝ) := by
    ext j
    by_cases h : j = e <;> simp [h]
  rw [he, map_smul]
  simp only [smul_eq_mul, mul_comm]

omit [Fintype E] in
lemma upward_functional_nonneg {D : Set (E → ℝ)} (hne : D.Nonempty)
    (hup : ∀ x ∈ D, ∀ y, (∀ e, x e ≤ y e) → y ∈ D)
    (f : (E → ℝ) →ₗ[ℝ] ℝ) (b : ℝ) (hb : ∀ x ∈ D, b < f x) :
    ∀ e, 0 ≤ f (Pi.single e 1) := by
  obtain ⟨x, hx⟩ := hne
  intro e
  by_contra hn
  have hn' : f (Pi.single e 1) < 0 := lt_of_not_ge hn
  let t := (f x - b + 1) / (-f (Pi.single e 1))
  have ht : 0 ≤ t := div_nonneg (by linarith [hb x hx]) (by linarith)
  have hy : x + t • Pi.single e 1 ∈ D := by
    apply hup x hx
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hi : 0 ≤ (Pi.single e (1:ℝ) : E → ℝ) i := by simp only [Pi.single_apply]; split_ifs <;> norm_num
    linarith [mul_nonneg ht hi]
  have h := hb _ hy
  rw [map_add, map_smul, smul_eq_mul] at h
  have he : t * f (Pi.single e 1) = -(f x - b + 1) := by
    dsimp [t]
    field_simp [ne_of_lt hn']
  rw [he] at h
  linarith

lemma subset_of_extreme_subset_upward {P D : Set (E → ℝ)}
    (hP : IsClosed P) (hP0 : ∀ x ∈ P, ∀ e, 0 ≤ x e)
    (hD : IsClosed D) (hDc : Convex ℝ D) (hD0 : ∀ x ∈ D, ∀ e, 0 ≤ x e)
    (hup : ∀ x ∈ D, ∀ y, (∀ e, x e ≤ y e) → y ∈ D)
    (hv : P.extremePoints ℝ ⊆ D) : P ⊆ D := by
  intro x hx
  by_contra hn
  obtain ⟨z, hz, _⟩ := exists_extreme_min_positive hP hP0 ⟨x, hx⟩ (fun _ => 1)
    (fun _ => by norm_num)
  have hne : D.Nonempty := ⟨z, hv hz⟩
  obtain ⟨f, b, hxb, hb⟩ := geometric_hahn_banach_point_closed hDc hD hn
  let c : E → ℝ := fun e => f (Pi.single e 1)
  have hc : ∀ e, 0 ≤ c e := upward_functional_nonneg hne hup f.toLinearMap b hb
  have hf (y : E → ℝ) : f y = linearCost c y := linear_eq_cost f.toLinearMap y
  let s := ∑ e, x e
  have hs : 0 ≤ s := Finset.sum_nonneg fun e _ => hP0 x hx e
  let ε := (b - f x) / (2 * (s + 1))
  have he : 0 < ε := div_pos (sub_pos.mpr hxb) (by positivity)
  have hes : ε * s < b - f x := by
    have hmul : ε * (2 * (s + 1)) = b - f x := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let d : E → ℝ := fun e => c e + ε
  have hd : ∀ e, 0 < d e := fun e => add_pos_of_nonneg_of_pos (hc e) he
  have heq (y : E → ℝ) : linearCost d y = f y + ε * ∑ e, y e := by
    rw [hf]
    simp only [linearCost_apply, d, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨w, hw, hmin⟩ := exists_extreme_min_positive hP hP0 ⟨x, hx⟩ d hd
  have hwD := hv hw
  have hlow := hb w hwD
  have hhigh := hmin x hx
  rw [heq w, heq x] at hhigh
  have hw0 : 0 ≤ ∑ e, w e := Finset.sum_nonneg fun e _ => hD0 w hwD e
  have hterm : 0 ≤ ε * ∑ e, w e := mul_nonneg he.le hw0
  change ε * (∑ e, x e) < b - f x at hes
  linarith

end ChinesePostman.Polyhedron.Proof
-- End PositiveGeneration

-- Begin DominantBasic

open scoped Pointwise
namespace ChinesePostman.Polyhedron.Proof

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def orthant (E : Type) : Set (E → ℝ) := {x | ∀ e, 0 ≤ x e}

omit [Fintype E] [DecidableEq E] in
lemma orthant_convex : Convex ℝ (orthant E) := by
  intro x hx y hy a b ha hb _ e
  exact add_nonneg (mul_nonneg ha (hx e)) (mul_nonneg hb (hy e))

omit [Fintype E] [DecidableEq E] in
lemma orthant_closed : IsClosed (orthant E) := by
  simp only [orthant, Set.ofPred_forall]
  exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)

omit [Fintype V] [Fintype E] in
lemma dominant_eq_add (G : Graph V E) (T : Finset V) :
    dominant G T = convexHull ℝ (joinPoints G T) + orthant E := by
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact Set.mem_add.mpr ⟨y,hy,x-y,fun e => sub_nonneg.mpr (hxy e),by abel⟩
  · intro h
    obtain ⟨y,hy,z,hz,rfl⟩ := Set.mem_add.mp h
    exact ⟨y,hy,fun e => le_add_of_nonneg_right (hz e)⟩

omit [Fintype V] in
lemma dominant_closed (G : Graph V E) (T : Finset V) : IsClosed (dominant G T) := by
  rw [dominant_eq_add]
  exact orthant_closed.add_left_of_isCompact ((joinPoints_finite G T).isCompact_convexHull (𝕜 := ℝ))

omit [Fintype V] [Fintype E] in
lemma dominant_convex (G : Graph V E) (T : Finset V) : Convex ℝ (dominant G T) := by
  rw [dominant_eq_add]
  exact (convex_convexHull ℝ _).add orthant_convex

omit [Fintype V] [Fintype E] in
lemma dominant_upward (G : Graph V E) (T : Finset V) {x y : E → ℝ}
    (hx : x ∈ dominant G T) (hxy : ∀ e, x e ≤ y e) : y ∈ dominant G T := by
  obtain ⟨z,hz,hzx⟩ := hx
  exact ⟨z,hz,fun e => (hzx e).trans (hxy e)⟩

omit [Fintype V] [Fintype E] in
lemma dominant_nonneg (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ dominant G T) : ∀ e, 0 ≤ x e := by
  obtain ⟨y,hy,hyx⟩ := hx
  have hsub : joinPoints G T ⊆ orthant E := by
    rintro z ⟨J,_,rfl⟩ e
    exact joinVector_nonneg J e
  have hh := convexHull_min hsub orthant_convex hy
  exact fun e => (hh e).trans (hyx e)

end ChinesePostman.Polyhedron.Proof
-- End DominantBasic

-- Begin CutTopology

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def cutLinear (G : Graph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun x := cutSum G x S
  map_add' x y := by simp [cutSum, Finset.sum_add_distrib]
  map_smul' a x := by simp [cutSum, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] [DecidableEq V] in
lemma cutLinear_apply (G : Graph V E) (S : Finset V) (x : E → ℝ) :
    cutLinear G S x = cutSum G x S := rfl

omit [Fintype V] [DecidableEq E] in
lemma cutPoly_closed (G : Graph V E) (T : Finset V) : IsClosed (CutPoly G T) := by
  change IsClosed ({x : E → ℝ | ∀ e, 0 ≤ x e} ∩
    {x | ∀ S : Finset V, Odd (S ∩ T).card → 1 ≤ cutSum G x S})
  apply orthant_closed.inter
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (cutLinear G S).continuous_of_finiteDimensional

omit [Fintype V] [DecidableEq E] in
lemma cutPoly_convex (G : Graph V E) (T : Finset V) : Convex ℝ (CutPoly G T) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_⟩
  intro S hS
  change 1 ≤ cutLinear G S (a • x + b • y)
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left (hx.2 S hS) ha)
    (mul_le_mul_of_nonneg_left (hy.2 S hS) hb)
  simp only [mul_one, hab] at h
  exact h

omit [Fintype V] [DecidableEq E] in
lemma cutPoly_upward (G : Graph V E) (T : Finset V) {x y : E → ℝ}
    (hx : x ∈ CutPoly G T) (hxy : ∀ e, x e ≤ y e) : y ∈ CutPoly G T := by
  refine ⟨fun e => (hx.1 e).trans (hxy e), fun S hS => ?_⟩
  exact (hx.2 S hS).trans (Finset.sum_le_sum (fun e _ => hxy e))

omit [Fintype V] in
lemma cutPoly_subset_dominant_of_extreme (G : Graph V E) (T : Finset V)
    (hv : (CutPoly G T).extremePoints ℝ ⊆ dominant G T) : CutPoly G T ⊆ dominant G T := by
  exact subset_of_extreme_subset_upward (cutPoly_closed G T) (fun _ hx => hx.1)
    (dominant_closed G T) (dominant_convex G T) (fun _ hx => dominant_nonneg G T hx)
    (fun _ hx _ hxy => dominant_upward G T hx hxy) hv

end ChinesePostman.Polyhedron.Proof
-- End CutTopology

-- Begin JoinParity

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in
lemma incident_join_nat (G : Graph V E) (J : Finset E) (v : V) :
    incidentSum G (fun e => if e ∈ J then (1:ℕ) else 0) v =
      (J.filter (fun e => v ∈ G.ends e)).card := by
  classical
  simp only [incidentSum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    smul_eq_mul, mul_one]
  congr 1
  ext e
  simp
  tauto

omit [Fintype V] in
lemma join_odd_cut (G : Graph V E) (T : Finset V) (J : Finset E) (hJ : IsJoin G T J)
    (S : Finset V) (hS : Odd (S ∩ T).card) :
    Odd (cutSum G (fun e => if e ∈ J then (1:ℕ) else 0) S) := by
  let x : E → ℕ := fun e => if e ∈ J then 1 else 0
  have hs : Odd (∑ v ∈ S, incidentSum G x v) := by
    rw [Finset.odd_sum_iff_odd_card_odd]
    have he : S.filter (fun v => Odd (incidentSum G x v)) = S ∩ T := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_inter]
      rw [incident_join_nat, hJ v]
    rwa [he]
  have hh := incident_cut_count G x S
  rw [Nat.odd_iff] at hs ⊢
  simp only [nsmul_eq_mul] at hh
  change cutSum G x S % 2 = 1
  omega

omit [Fintype V] in
lemma joinVector_mem_cutPoly (G : Graph V E) (T : Finset V) (J : Finset E)
    (hJ : IsJoin G T J) : joinVector J ∈ CutPoly G T := by
  refine ⟨joinVector_nonneg J,fun S hS => ?_⟩
  have ho := join_odd_cut G T J hJ S hS
  have hn : 1 ≤ cutSum G (fun e => if e ∈ J then (1:ℕ) else 0) S := by
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at ho)
  have he : ((cutSum G (fun e => if e ∈ J then (1:ℕ) else 0) S : ℕ) : ℝ) =
      cutSum G (joinVector J) S := by
    simp [cutSum,joinVector]
  exact_mod_cast he ▸ (show (1:ℝ) ≤ (cutSum G (fun e => if e ∈ J then (1:ℕ) else 0) S : ℕ) from by exact_mod_cast hn)

omit [Fintype V] in
lemma dominant_subset_cutPoly (G : Graph V E) (T : Finset V) : dominant G T ⊆ CutPoly G T := by
  rintro x ⟨y,hy,hyx⟩
  apply cutPoly_upward G T (convexHull_min ?_ (cutPoly_convex G T) hy) hyx
  rintro z ⟨J,hJ,rfl⟩
  exact joinVector_mem_cutPoly G T J hJ

end ChinesePostman.Polyhedron.Proof
-- End JoinParity

-- Begin TightMixture

namespace ChinesePostman.Polyhedron.Proof
variable {I E : Type} [Fintype I] [DecidableEq E]

omit [DecidableEq E] in
lemma tight_mixture (C : Finset E) (a : I → ℝ) (b : I → E → ℝ) (x : E → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hb : ∀ i, 1 ≤ ∑ e ∈ C, b i e)
    (hbound : ∀ e ∈ C, (∑ i, a i * b i e) ≤ x e) (hx : ∑ e ∈ C, x e = 1) :
    (∀ e ∈ C, (∑ i, a i * b i e) = x e) ∧
    (∀ i, 0 < a i → ∑ e ∈ C, b i e = 1) := by
  have hex : (∑ e ∈ C, ∑ i, a i * b i e) = ∑ i, a i * ∑ e ∈ C, b i e := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hlo : 1 ≤ ∑ e ∈ C, ∑ i, a i * b i e := by
    rw [hex, ← ha1]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hb i,ha i]
  have hhi : (∑ e ∈ C, ∑ i, a i * b i e) ≤ 1 := by
    rw [← hx]
    exact Finset.sum_le_sum hbound
  have heq : (∑ e ∈ C, ∑ i, a i * b i e) = 1 := le_antisymm hhi hlo
  constructor
  · have hs : ∑ e ∈ C, (x e - ∑ i, a i * b i e) = 0 := by
      rw [Finset.sum_sub_distrib,hx,heq,sub_self]
    intro e he
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun e he => sub_nonneg.mpr (hbound e he))).mp hs e he
    linarith
  · have hs : ∑ i, a i * ((∑ e ∈ C, b i e) - 1) = 0 := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
      rw [← hex,heq,ha1,sub_self]
    intro i hi
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (ha j) (sub_nonneg.mpr (hb j)))).mp hs i (Finset.mem_univ i)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hi.ne')

end ChinesePostman.Polyhedron.Proof
-- End TightMixture

-- Begin ContractionMixture

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in
lemma incident_join_real (G : Graph V E) (J : Finset E) (v : V) :
    incidentSum G (joinVector J) v = ((J.filter (fun e => v ∈ G.ends e)).card : ℝ) := by
  have h := congrArg (fun n : ℕ => (n:ℝ)) (incident_join_nat G J v)
  simpa [incidentSum,joinVector] using h

lemma contraction_tight_mixture (G : Graph V E) (S T : Finset V) (x : E → ℝ)
    (hS : Odd (S ∩ T).card) (hT : Even T.card) (hx : cutSum G x S = 1)
    {I : Type} [Fintype I] (a : I → ℝ)
    (J : I → Finset {e // Survives G (collapseVertex S) e})
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hJ : ∀ i, IsJoin (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)) (J i))
    (hb : ∀ e, (∑ i, a i * joinVector (J i) e) ≤ x e.val) :
    (∀ e : {e // Survives G (collapseVertex S) e}, Meets G e.val S →
      (∑ i, a i * joinVector (J i) e) = x e.val) ∧
    (∀ i, 0 < a i → (J i |>.filter (fun e => none ∈ (quotientGraph G (collapseVertex S)).ends e)).card = 1) := by
  classical
  let Q := quotientGraph G (collapseVertex S)
  let C : Finset {e // Survives G (collapseVertex S) e} := Finset.univ.filter (fun e => none ∈ Q.ends e)
  have hnone := pushParity_collapse_none_of_odd S T hS hT
  have hlow (i : I) : 1 ≤ ∑ e ∈ C, joinVector (J i) e := by
    exact (cutPoly_degree Q _ (joinVector_mem_cutPoly Q _ (J i) (hJ i))).2 none hnone
  have hsum : ∑ e ∈ C, x e.val = 1 := by
    change incidentSum Q (fun e => x e.val) none = 1
    rw [fresh_cutSum]
    exact hx
  obtain ⟨hm,hi⟩ := tight_mixture C a (fun i => joinVector (J i)) (fun e => x e.val)
    ha ha1 hlow (fun e _ => hb e) hsum
  refine ⟨fun e he => hm e ?_,fun i hai => ?_⟩
  · simp only [C,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (fresh_incident_iff G S e).mpr he
  · have hh := hi i hai
    change incidentSum Q (joinVector (J i)) none = 1 at hh
    rw [incident_join_real] at hh
    exact_mod_cast hh

end ChinesePostman.Polyhedron.Proof
-- End ContractionMixture

-- Begin LiftJoin

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def liftEdges {P : E → Prop} (J : Finset {e // P e}) : Finset E :=
  J.image Subtype.val

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma mem_liftEdges {P : E → Prop} (J : Finset {e // P e}) (e : E) :
    e ∈ liftEdges J ↔ ∃h : P e, (⟨e,h⟩ : {e // P e}) ∈ J := by
  classical
  simp only [liftEdges,Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.property,ha⟩
  · rintro ⟨h,hh⟩
    exact ⟨⟨e,h⟩,hh,rfl⟩

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma liftEdges_property {P : E → Prop} (J : Finset {e // P e}) {e : E}
    (he : e ∈ liftEdges J) : P e := (mem_liftEdges J e).mp he |>.choose

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma retained_incident_iff (G : Graph V E) (S : Finset V) (v : {v // v ∈ S})
    (e : {e // Survives G (collapseVertex S) e}) :
    some v ∈ (quotientGraph G (collapseVertex S)).ends e ↔ v.val ∈ G.ends e.val := by
  change some v ∈ (G.ends e.val).map (collapseVertex S) ↔ _
  rw [Sym2.mem_map]
  simp only [collapse_some,exists_eq_right]

omit [Fintype V] [Fintype E] in
lemma lift_incident_card (G : Graph V E) (S : Finset V)
    (J : Finset {e // Survives G (collapseVertex S) e}) (v : {v // v ∈ S}) :
    (J.filter (fun e => some v ∈ (quotientGraph G (collapseVertex S)).ends e)).card =
      ((liftEdges J).filter (fun e => v.val ∈ G.ends e)).card := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    obtain ⟨heJ,hev⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(mem_liftEdges J e.val).mpr ⟨e.property,heJ⟩,
      (retained_incident_iff G S v e).mp hev⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro e he
    obtain ⟨heJ,hev⟩ := Finset.mem_filter.mp he
    obtain ⟨h,hh⟩ := (mem_liftEdges J e).mp heJ
    exact ⟨⟨e,h⟩,Finset.mem_filter.mpr ⟨hh,(retained_incident_iff G S v _).mpr hev⟩,rfl⟩

omit [Fintype V] [Fintype E] in
lemma lift_join_retained (G : Graph V E) (S T : Finset V)
    (J : Finset {e // Survives G (collapseVertex S) e})
    (hJ : IsJoin (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)) J)
    {v : V} (hv : v ∈ S) :
    Odd ((liftEdges J).filter (fun e => v ∈ G.ends e)).card ↔ v ∈ T := by
  have h := hJ (some ⟨v,hv⟩)
  rw [lift_incident_card,pushParity_collapse_some] at h
  exact h

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma mem_liftEdges_subtype {P : E → Prop} (J : Finset {e // P e}) (e : {e // P e}) :
    e.val ∈ liftEdges J ↔ e ∈ J := by
  classical
  rw [mem_liftEdges]
  constructor
  · rintro ⟨h,hh⟩
    exact hh
  · intro h
    exact ⟨e.property,h⟩

lemma lift_crossing_card (G : Graph V E) (S : Finset V)
    (J : Finset {e // Survives G (collapseVertex S) e}) :
    (J.filter (fun e => none ∈ (quotientGraph G (collapseVertex S)).ends e)).card =
      (liftEdges J ∩ cutEdges G S).card := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    obtain ⟨hJ,hv⟩ := Finset.mem_filter.mp he
    exact Finset.mem_inter.mpr ⟨(mem_liftEdges_subtype J e).mpr hJ,
      (mem_cutEdges G S e.val).mpr ((fresh_incident_iff G S e).mp hv)⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro e he
    obtain ⟨hJ,hv⟩ := Finset.mem_inter.mp he
    obtain ⟨h,hh⟩ := (mem_liftEdges J e).mp hJ
    exact ⟨⟨e,h⟩,Finset.mem_filter.mpr ⟨hh,
      (fresh_incident_iff G S _).mpr ((mem_cutEdges G S e).mp hv)⟩,rfl⟩

end ChinesePostman.Polyhedron.Proof
-- End LiftJoin

-- Begin FiniteCoupling

open Classical
namespace ChinesePostman.Polyhedron.Proof
variable {I J K : Type} [Fintype I] [Fintype J]

noncomputable def fiberMass (a : I → ℝ) (l : I → K) (k : K) : ℝ :=
  ∑i, if l i = k then a i else 0

noncomputable def finiteCoupling (a : I → ℝ) (b : J → ℝ) (l : I → K) (r : J → K) : I × J → ℝ :=
  fun p => if l p.1 = r p.2 then a p.1 * b p.2 / fiberMass a l (l p.1) else 0

lemma fiberMass_nonneg (a : I → ℝ) (l : I → K) (ha : ∀i,0 ≤ a i) (k : K) :
    0 ≤ fiberMass a l k := by
  classical
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact ha i
  · rfl

lemma le_fiberMass (a : I → ℝ) (l : I → K) (ha : ∀i,0 ≤ a i) (i : I) :
    a i ≤ fiberMass a l (l i) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if l j = l i then a j else 0)
    (fun j _ => by split_ifs; exact ha j; rfl) (Finset.mem_univ i)
  simpa [fiberMass] using h

omit [Fintype J] in
lemma finiteCoupling_nonneg (a : I → ℝ) (b : J → ℝ) (l : I → K) (r : J → K)
    (ha : ∀i,0 ≤ a i) (hb : ∀j,0 ≤ b j) (p : I × J) :
    0 ≤ finiteCoupling a b l r p := by
  classical
  unfold finiteCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (ha _) (hb _)) (fiberMass_nonneg a l ha _)
  · rfl

lemma finiteCoupling_row (a : I → ℝ) (b : J → ℝ) (l : I → K) (r : J → K)
    (ha : ∀i,0 ≤ a i)
    (hm : ∀k, fiberMass a l k = fiberMass b r k) (i : I) :
    ∑j, finiteCoupling a b l r (i,j) = a i := by
  classical
  by_cases hz : fiberMass a l (l i) = 0
  · have hai : a i = 0 := le_antisymm (by simpa [hz] using le_fiberMass a l ha i) (ha i)
    simp [finiteCoupling,hai]
  · calc
      ∑j, finiteCoupling a b l r (i,j) =
          a i / fiberMass a l (l i) * fiberMass b r (l i) := by
        simp only [finiteCoupling,fiberMass,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : l i = r j
        · rw [if_pos h,if_pos h.symm]
          ring
        · simp [h,Ne.symm h]
      _ = a i := by rw [←hm,div_mul_cancel₀ _ hz]

lemma finiteCoupling_swap (a : I → ℝ) (b : J → ℝ) (l : I → K) (r : J → K)
    (hm : ∀k, fiberMass a l k = fiberMass b r k) (i : I) (j : J) :
    finiteCoupling a b l r (i,j) = finiteCoupling b a r l (j,i) := by
  classical
  by_cases h : l i = r j
  · simp only [finiteCoupling,h,if_true]
    rw [hm]
    ring
  · simp [finiteCoupling,h,Ne.symm h]

lemma exists_finite_coupling (a : I → ℝ) (b : J → ℝ) (l : I → K) (r : J → K)
    (ha : ∀i,0 ≤ a i) (hb : ∀j,0 ≤ b j) (ha1 : ∑i,a i = 1)
    (hm : ∀k, fiberMass a l k = fiberMass b r k) :
    ∃q : I × J → ℝ, (∀p,0 ≤ q p) ∧ (∀i,∑j,q (i,j) = a i) ∧
      (∀j,∑i,q (i,j) = b j) ∧ (∑p,q p = 1) ∧ ∀i j, 0 < q (i,j) → l i = r j := by
  classical
  refine ⟨finiteCoupling a b l r,finiteCoupling_nonneg a b l r ha hb,
    finiteCoupling_row a b l r ha hm,?_,?_,?_⟩
  · intro j
    simp_rw [finiteCoupling_swap a b l r hm]
    exact finiteCoupling_row b a r l hb (fun k => (hm k).symm) j
  · rw [Fintype.sum_prod_type]
    simp_rw [finiteCoupling_row a b l r ha hm]
    exact ha1
  · intro i j h
    by_contra hn
    simp [finiteCoupling,hn] at h

end ChinesePostman.Polyhedron.Proof
-- End FiniteCoupling

-- Begin CrossingLabels

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma contraction_mixture_labels (G : Graph V E) (S T : Finset V) (x : E → ℝ)
    (hS : Odd (S ∩ T).card) (hT : Even T.card) (hx : cutSum G x S = 1)
    {I : Type} [Fintype I] (a : I → ℝ)
    (J : I → Finset {e // Survives G (collapseVertex S) e})
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hJ : ∀ i, IsJoin (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)) (J i))
    (hb : ∀ e, (∑ i, a i * joinVector (J i) e) ≤ x e.val) :
    ∃ l : I → E, (∀ i, l i ∈ cutEdges G S) ∧
      (∀ i, 0 < a i → liftEdges (J i) ∩ cutEdges G S = {l i}) ∧
      ∀ e, fiberMass a l e = if e ∈ cutEdges G S then x e else 0 := by
  classical
  obtain ⟨hm,hcard⟩ := contraction_tight_mixture G S T x hS hT hx a J ha ha1 hJ hb
  have hne : (cutEdges G S).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    change ∑ e ∈ cutEdges G S, x e = 1 at hx
    rw [he,Finset.sum_empty] at hx
    norm_num at hx
  obtain ⟨e₀,he₀⟩ := hne
  have hex (i : I) : ∃ e, e ∈ cutEdges G S ∧ (0 < a i → liftEdges (J i) ∩ cutEdges G S = {e}) := by
    by_cases hi : 0 < a i
    · have hh := hcard i hi
      rw [lift_crossing_card] at hh
      obtain ⟨e,he⟩ := Finset.card_eq_one.mp hh
      refine ⟨e,?_,fun _ => he⟩
      have : e ∈ liftEdges (J i) ∩ cutEdges G S := by rw [he]; simp
      exact (Finset.mem_inter.mp this).2
    · exact ⟨e₀,he₀,fun h => (hi h).elim⟩
  choose l hl hsingle using hex
  refine ⟨l,hl,hsingle,fun e => ?_⟩
  by_cases he : e ∈ cutEdges G S
  · rw [if_pos he]
    have hecut := (mem_cutEdges G S e).mp he
    let q : {e // Survives G (collapseVertex S) e} := ⟨e,meets_survives_collapse G S hecut⟩
    rw [← hm q hecut]
    unfold fiberMass
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < a i
    · have hiq : q ∈ J i ↔ l i = e := by
        rw [← mem_liftEdges_subtype]
        change e ∈ liftEdges (J i) ↔ l i = e
        have hh := hsingle i hi
        have hmem := congrArg (fun A : Finset E => e ∈ A) hh
        have hh : e ∈ liftEdges (J i) ↔ e = l i := by
          simpa only [Finset.mem_inter,he,and_true,Finset.mem_singleton] using Iff.of_eq hmem
        exact hh.trans eq_comm
      simp only [joinVector,hiq]
      split_ifs <;> simp
    · have hi0 : a i = 0 := le_antisymm (le_of_not_gt hi) (ha i)
      simp [hi0]
  · rw [if_neg he]
    unfold fiberMass
    apply Finset.sum_eq_zero
    intro i _
    have hne : l i ≠ e := fun hh => he (hh ▸ hl i)
    simp [hne]

end ChinesePostman.Polyhedron.Proof
-- End CrossingLabels

-- Begin GlueJoin

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma lift_union_incident (G : Graph V E) (S : Finset V)
    (J1 : Finset {e // Survives G (collapseVertex S) e})
    (J2 : Finset {e // Survives G (collapseVertex Sᶜ) e}) (e : E)
    (h1 : liftEdges J1 ∩ cutEdges G S = {e})
    (h2 : liftEdges J2 ∩ cutEdges G S = {e})
    {v : V} (hv : v ∈ S) :
    ((liftEdges J1 ∪ liftEdges J2).filter (fun a => v ∈ G.ends a)) =
      ((liftEdges J1).filter (fun a => v ∈ G.ends a)) := by
  classical
  ext a
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨ha|ha,hav⟩
    · exact ⟨ha,hav⟩
    · have hs : Survives G (collapseVertex S) a :=
        (survives_collapse G S a).mpr ⟨v,hav,hv⟩
      have hc := (survives_both_iff_meets G S a).mp ⟨hs,liftEdges_property J2 ha⟩
      have hmem : a ∈ liftEdges J2 ∩ cutEdges G S :=
        Finset.mem_inter.mpr ⟨ha,(mem_cutEdges G S a).mpr hc⟩
      rw [h2,Finset.mem_singleton] at hmem
      subst a
      have he : e ∈ liftEdges J1 ∩ cutEdges G S := by rw [h1]; simp
      exact ⟨(Finset.mem_inter.mp he).1,hav⟩
  · rintro ⟨ha,hav⟩
    exact ⟨Or.inl ha,hav⟩

omit [DecidableEq E] in
lemma cutEdges_compl (G : Graph V E) (S : Finset V) :
    cutEdges G Sᶜ = cutEdges G S := by
  classical
  ext e
  rw [mem_cutEdges,mem_cutEdges,meets_compl]

lemma glue_join (G : Graph V E) (S T : Finset V)
    (J1 : Finset {e // Survives G (collapseVertex S) e})
    (J2 : Finset {e // Survives G (collapseVertex Sᶜ) e})
    (hJ1 : IsJoin (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)) J1)
    (hJ2 : IsJoin (quotientGraph G (collapseVertex Sᶜ)) (pushParity T (collapseVertex Sᶜ)) J2)
    (e : E) (h1 : liftEdges J1 ∩ cutEdges G S = {e})
    (h2 : liftEdges J2 ∩ cutEdges G S = {e}) :
    IsJoin G T (liftEdges J1 ∪ liftEdges J2) := by
  classical
  intro v
  by_cases hv : v ∈ S
  · rw [lift_union_incident G S J1 J2 e h1 h2 hv]
    exact lift_join_retained G S T J1 hJ1 hv
  · have hvc : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    have hi : ((liftEdges J1 ∪ liftEdges J2).filter (fun a => v ∈ G.ends a)) =
        ((liftEdges J2).filter (fun a => v ∈ G.ends a)) := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_union]
      constructor
      · rintro ⟨ha|ha,hav⟩
        · have hs : Survives G (collapseVertex Sᶜ) a :=
            (survives_collapse G Sᶜ a).mpr ⟨v,hav,hvc⟩
          have hc := (survives_both_iff_meets G S a).mp ⟨liftEdges_property J1 ha,hs⟩
          have hm : a ∈ liftEdges J1 ∩ cutEdges G S :=
            Finset.mem_inter.mpr ⟨ha,(mem_cutEdges G S a).mpr hc⟩
          rw [h1,Finset.mem_singleton] at hm
          subst a
          have he : e ∈ liftEdges J2 ∩ cutEdges G S := by rw [h2]; simp
          exact ⟨(Finset.mem_inter.mp he).1,hav⟩
        · exact ⟨ha,hav⟩
      · rintro ⟨ha,hav⟩
        exact ⟨Or.inr ha,hav⟩
    rw [hi]
    exact lift_join_retained G Sᶜ T J2 hJ2 hvc

lemma lift_union_mem_of_survives (G : Graph V E) (S : Finset V)
    (J1 : Finset {e // Survives G (collapseVertex S) e})
    (J2 : Finset {e // Survives G (collapseVertex Sᶜ) e}) (e : E)
    (h1 : liftEdges J1 ∩ cutEdges G S = {e})
    (h2 : liftEdges J2 ∩ cutEdges G S = {e})
    {a : E} (ha : Survives G (collapseVertex S) a) :
    a ∈ liftEdges J1 ∪ liftEdges J2 ↔ a ∈ liftEdges J1 := by
  classical
  rw [Finset.mem_union]
  constructor
  · rintro (h|h)
    · exact h
    · have hc := (survives_both_iff_meets G S a).mp ⟨ha,liftEdges_property J2 h⟩
      have hm : a ∈ liftEdges J2 ∩ cutEdges G S :=
        Finset.mem_inter.mpr ⟨h,(mem_cutEdges G S a).mpr hc⟩
      rw [h2,Finset.mem_singleton] at hm
      subst a
      have he : e ∈ liftEdges J1 ∩ cutEdges G S := by rw [h1]; simp
      exact (Finset.mem_inter.mp he).1
  · exact Or.inl

lemma lift_union_mem_of_survives_compl (G : Graph V E) (S : Finset V)
    (J1 : Finset {e // Survives G (collapseVertex S) e})
    (J2 : Finset {e // Survives G (collapseVertex Sᶜ) e}) (e : E)
    (h1 : liftEdges J1 ∩ cutEdges G S = {e})
    (h2 : liftEdges J2 ∩ cutEdges G S = {e})
    {a : E} (ha : Survives G (collapseVertex Sᶜ) a) :
    a ∈ liftEdges J1 ∪ liftEdges J2 ↔ a ∈ liftEdges J2 := by
  classical
  rw [Finset.mem_union]
  constructor
  · rintro (h|h)
    · have hc := (survives_both_iff_meets G S a).mp ⟨liftEdges_property J1 h,ha⟩
      have hm : a ∈ liftEdges J1 ∩ cutEdges G S :=
        Finset.mem_inter.mpr ⟨h,(mem_cutEdges G S a).mpr hc⟩
      rw [h1,Finset.mem_singleton] at hm
      subst a
      have he : e ∈ liftEdges J2 ∩ cutEdges G S := by rw [h2]; simp
      exact (Finset.mem_inter.mp he).1
    · exact h
  · exact Or.inr

end ChinesePostman.Polyhedron.Proof
-- End GlueJoin

-- Begin JoinMixture

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] in
lemma dominant_mixture (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ dominant G T) :
    ∃ (I : Type) (_ : Fintype I) (a : I → ℝ) (J : I → Finset E),
      (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧ (∀ i, IsJoin G T (J i)) ∧
      ∀ e, (∑ i, a i * joinVector (J i) e) ≤ x e := by
  classical
  obtain ⟨y,hy,hyx⟩ := hx
  obtain ⟨I,hI,a,z,ha,ha1,hz,heq⟩ := mem_convexHull_iff_exists_fintype.mp hy
  choose J hJ hJeq using hz
  refine ⟨I,hI,a,J,ha,ha1,hJ,fun e => ?_⟩
  have hh := congrFun heq e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simp_rw [hJeq] at hh
  rw [hh]
  exact hyx e

omit [Fintype V] [Fintype E] in
lemma mixture_mem_dominant (G : Graph V E) (T : Finset V) {x : E → ℝ}
    {I : Type} [Fintype I] (a : I → ℝ) (J : I → Finset E)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (hJ : ∀ i, IsJoin G T (J i))
    (hbound : ∀ e, (∑ i, a i * joinVector (J i) e) ≤ x e) : x ∈ dominant G T := by
  refine ⟨∑ i, a i • joinVector (J i),?_,?_⟩
  · exact mem_convexHull_of_exists_fintype a (fun i => joinVector (J i)) ha ha1
      (fun i => ⟨J i,hJ i,rfl⟩) rfl
  · intro e
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hbound e

end ChinesePostman.Polyhedron.Proof
-- End JoinMixture

-- Begin PositiveMixture

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma positive_mixture_mem_dominant (G : Graph V E) (T : Finset V) {x : E → ℝ}
    {I : Type} [Fintype I] (a : I → ℝ) (J : I → Finset E)
    (ha : ∀i,0 ≤ a i) (ha1 : ∑i,a i = 1)
    (hJ : ∀i,0 < a i → IsJoin G T (J i))
    (hb : ∀e,(∑i,a i * joinVector (J i) e) ≤ x e) : x ∈ dominant G T := by
  classical
  have hp : ∃i,0 < a i := by
    by_contra hn
    push Not at hn
    have hs : ∑i,a i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i₀,hi₀⟩ := hp
  let J' : I → Finset E := fun i => if 0 < a i then J i else J i₀
  apply mixture_mem_dominant G T a J' ha ha1
  · intro i
    dsimp [J']
    split_ifs with h
    · exact hJ i h
    · exact hJ i₀ hi₀
  · intro e
    convert hb e using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [J']
    split_ifs with h
    · rfl
    · have hz : a i = 0 := le_antisymm (le_of_not_gt h) (ha i)
      simp [hz]

end ChinesePostman.Polyhedron.Proof
-- End PositiveMixture

-- Begin CoupledSum

namespace ChinesePostman.Polyhedron.Proof
variable {I J : Type} [Fintype I] [Fintype J]

lemma coupled_sum_left (q : I × J → ℝ) (a : I → ℝ) (u : I → ℝ) (z : I × J → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hrow : ∀ i, ∑ j, q (i,j) = a i)
    (hz : ∀ i j, 0 < q (i,j) → z (i,j) = u i) :
    (∑ p, q p * z p) = ∑ i, a i * u i := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, q (i,j) * z (i,j)) = ∑ j, q (i,j) * u i := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : 0 < q (i,j)
      · rw [hz i j h]
      · have hh : q (i,j) = 0 := le_antisymm (le_of_not_gt h) (hq _)
        simp [hh]
    _ = a i * u i := by rw [← Finset.sum_mul,hrow]

lemma coupled_sum_right (q : I × J → ℝ) (b : J → ℝ) (u : J → ℝ) (z : I × J → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hcol : ∀ j, ∑ i, q (i,j) = b j)
    (hz : ∀ i j, 0 < q (i,j) → z (i,j) = u j) :
    (∑ p, q p * z p) = ∑ j, b j * u j := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i, q (i,j) * z (i,j)) = ∑ i, q (i,j) * u j := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 < q (i,j)
      · rw [hz i j h]
      · have hh : q (i,j) = 0 := le_antisymm (le_of_not_gt h) (hq _)
        simp [hh]
    _ = b j * u j := by rw [← Finset.sum_mul,hcol]

lemma positive_coupling_marginals (q : I × J → ℝ) (a : I → ℝ) (b : J → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hrow : ∀ i, ∑ j, q (i,j) = a i)
    (hcol : ∀ j, ∑ i, q (i,j) = b j) {i : I} {j : J} (hp : 0 < q (i,j)) :
    0 < a i ∧ 0 < b j := by
  constructor
  · rw [← hrow]
    exact hp.trans_le (Finset.single_le_sum (fun k _ => hq (i,k)) (Finset.mem_univ j))
  · rw [← hcol]
    exact hp.trans_le (Finset.single_le_sum (fun k _ => hq (k,j)) (Finset.mem_univ i))

end ChinesePostman.Polyhedron.Proof
-- End CoupledSum

-- Begin CutKernel

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def cutRows (G : Graph V E) (T : Finset V) :
    E ⊕ {S : Finset V // Odd (S ∩ T).card} → (E → ℝ) →ₗ[ℝ] ℝ
  | Sum.inl e => -(LinearMap.proj e)
  | Sum.inr S => -(cutLinear G S)

def cutRhs (T : Finset V) : E ⊕ {S : Finset V // Odd (S ∩ T).card} → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

omit [Fintype V] [DecidableEq E] in
lemma cutPoly_eq (G : Graph V E) (T : Finset V) :
    CutPoly G T = polyBody (cutRows G T) (cutRhs T) := by
  ext x
  constructor
  · rintro ⟨hx,hS⟩ (e|S)
    · simpa [cutRows,cutRhs] using hx e
    · simpa [cutRows,cutRhs,cutLinear_apply] using hS S S.property
  · intro h
    refine ⟨fun e => ?_,fun S hS => ?_⟩
    · simpa [cutRows,cutRhs] using h (Sum.inl e)
    · simpa [cutRows,cutRhs,cutLinear_apply] using h (Sum.inr ⟨S,hS⟩)

omit [DecidableEq E] in
lemma cut_vertex_kernel (G : Graph V E) (T : Finset V) {x d : E → ℝ}
    (hx : x ∈ (CutPoly G T).extremePoints ℝ)
    (hz : ∀ e, x e = 0 → d e = 0)
    (ht : ∀ S : Finset V, Odd (S ∩ T).card → cutSum G x S = 1 → cutSum G d S = 0) : d = 0 := by
  rw [cutPoly_eq] at hx
  apply vertex_kernel_zero hx
  rintro (e|S) h
  · have he : x e = 0 := by simpa [cutRows,cutRhs] using h
    simp [cutRows,hz e he]
  · have he : cutSum G x S = 1 := by simpa [cutRows,cutRhs,cutLinear_apply] using h
    simp [cutRows,cutLinear_apply,ht S S.property he]

lemma odd_compl_inter_iff (S T : Finset V) (hT : Even T.card) :
    Odd (Sᶜ ∩ T).card ↔ Odd (S ∩ T).card := by
  have heq : Sᶜ ∩ T = T \ S := by ext v; simp; tauto
  rw [heq, Nat.odd_iff, Nat.odd_iff]
  have hc := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hc
  have he := Nat.even_iff.mp hT
  omega

end ChinesePostman.Polyhedron.Proof
-- End CutKernel

-- Begin GlueMixtures

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma glue_dominated_mixtures (G : Graph V E) (S T : Finset V) (x : E → ℝ)
    (hS : Odd (S ∩ T).card) (hT : Even T.card) (hx : cutSum G x S = 1)
    (h1 : (fun e => x e.val) ∈ dominant (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)))
    (h2 : (fun e => x e.val) ∈ dominant (quotientGraph G (collapseVertex Sᶜ)) (pushParity T (collapseVertex Sᶜ))) :
    x ∈ dominant G T := by
  classical
  obtain ⟨I,hI,a,J1,ha,ha1,hJ1,hb1⟩ := dominant_mixture _ _ h1
  obtain ⟨K,hK,b,J2,hb,hb1sum,hJ2,hb2⟩ := dominant_mixture _ _ h2
  obtain ⟨l,_,hl,hlm⟩ := contraction_mixture_labels G S T x hS hT hx a J1 ha ha1 hJ1 hb1
  have hSc : Odd (Sᶜ ∩ T).card := (odd_compl_inter_iff S T hT).mpr hS
  have hxc : cutSum G x Sᶜ = 1 := by rwa [cutSum_compl]
  obtain ⟨r,_,hr,hrm⟩ := contraction_mixture_labels G Sᶜ T x hSc hT hxc b J2 hb hb1sum hJ2 hb2
  simp_rw [cutEdges_compl] at hr hrm
  obtain ⟨q,hq,hrow,hcol,hq1,hequal⟩ := exists_finite_coupling a b l r ha hb ha1 (fun e => by rw [hlm,hrm])
  let J : I × K → Finset E := fun p => liftEdges (J1 p.1) ∪ liftEdges (J2 p.2)
  apply positive_mixture_mem_dominant G T q J hq hq1
  · rintro ⟨i,j⟩ hp
    obtain ⟨hi,hj⟩ := positive_coupling_marginals q a b hq hrow hcol hp
    have hh2 := hr j hj
    rw [← hequal i j hp] at hh2
    exact glue_join G S T (J1 i) (J2 j) (hJ1 i) (hJ2 j) (l i) (hl i hi) hh2
  · intro e
    by_cases he : Survives G (collapseVertex S) e
    · let v : {e // Survives G (collapseVertex S) e} := ⟨e,he⟩
      have heq := coupled_sum_left q a (fun i => joinVector (J1 i) v)
        (fun p => joinVector (J p) e) hq hrow (fun i j hp => ?_)
      · rw [heq]
        exact hb1 v
      · obtain ⟨hi,hj⟩ := positive_coupling_marginals q a b hq hrow hcol hp
        have hh2 := hr j hj
        rw [← hequal i j hp] at hh2
        have hm := lift_union_mem_of_survives G S (J1 i) (J2 j) (l i) (hl i hi) hh2 he
        have hm' : e ∈ J (i,j) ↔ v ∈ J1 i := hm.trans (mem_liftEdges_subtype (J1 i) v)
        simp only [joinVector,hm']
    · have he' : Survives G (collapseVertex Sᶜ) e := (survives_one G S e).resolve_left he
      let v : {e // Survives G (collapseVertex Sᶜ) e} := ⟨e,he'⟩
      have heq := coupled_sum_right q b (fun j => joinVector (J2 j) v)
        (fun p => joinVector (J p) e) hq hcol (fun i j hp => ?_)
      · rw [heq]
        exact hb2 v
      · obtain ⟨hi,hj⟩ := positive_coupling_marginals q a b hq hrow hcol hp
        have hh2 := hr j hj
        rw [← hequal i j hp] at hh2
        have hm := lift_union_mem_of_survives_compl G S (J1 i) (J2 j) (l i) (hl i hi) hh2 he'
        have hm' : e ∈ J (i,j) ↔ v ∈ J2 j := hm.trans (mem_liftEdges_subtype (J2 j) v)
        simp only [joinVector,hm']

end ChinesePostman.Polyhedron.Proof
-- End GlueMixtures

-- Begin SupportIndependent

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def tightVertices (G : Graph V E) (T : Finset V) (x : E → ℝ) : Finset V :=
  T.filter (fun v => incidentSum G x v = 1)

noncomputable def positiveEdges (x : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => 0 < x e)

noncomputable def incidenceColumn (G : Graph V E) (R : Finset V) (e : E) : R → ℝ :=
  fun v => if v.val ∈ G.ends e then 1 else 0

omit [Fintype V] in
lemma support_columns_independent (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) :
    LinearIndependent ℝ (fun e : positiveEdges x => incidenceColumn G (tightVertices G T x) e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let d : E → ℝ := ∑ e : positiveEdges x, a e • Pi.single e.val (1 : ℝ)
  have hval (e : positiveEdges x) : d e.val = a e := by
    simp only [d,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      have hne : j.val ≠ e.val := fun h => hj (Subtype.ext h)
      simp [Ne.symm hne]
    · simp
  have hd : d = 0 := degree_vertex_kernel G T hx (by
    intro e he
    simp only [d,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have hj : 0 < x j.val := by simpa [positiveEdges] using j.property
    have hne : j.val ≠ e := by intro h; simp [h,he] at hj
    simp [Ne.symm hne]) (by
    intro v hv hvt
    have hvR : v ∈ tightVertices G T x := by simp [tightVertices,hv,hvt]
    have h := congrFun ha ⟨v,hvR⟩
    change (incidentLinear G v) d = 0
    simpa [d,map_sum,incident_single,incidenceColumn,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul] using h)
  intro e
  rw [←hval e,hd]
  rfl

omit [Fintype V] in
lemma positive_has_tight_endpoint (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) {e : E} (he : 0 < x e) :
    ∃v∈tightVertices G T x, v ∈ G.ends e := by
  classical
  have heP : e ∈ positiveEdges x := by simp [positiveEdges,he]
  have hn := (support_columns_independent G T hx).ne_zero ⟨e,heP⟩
  by_contra h
  apply hn
  ext v
  simp only [incidenceColumn,Pi.zero_apply]
  have hv : v.val ∉ G.ends e := fun hh => h ⟨v.val,v.property,hh⟩
  simp [hv]

omit [Fintype V] in
lemma positive_le_one (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (e : E) : x e ≤ 1 := by
  by_cases he : 0 < x e
  · obtain ⟨v,hv,hev⟩ := positive_has_tight_endpoint G T hx he
    have ht : incidentSum G x v = 1 := (Finset.mem_filter.mp hv).2
    simpa [ht] using coordinate_le_incident G hx.1.1 hev
  · linarith

omit [Fintype V] in
lemma positive_ends_injective (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) :
    Function.Injective (fun e : positiveEdges x => G.ends e.val) := by
  intro e f h
  apply (support_columns_independent G T hx).injective
  ext v
  simp [incidenceColumn,h]

end ChinesePostman.Polyhedron.Proof
-- End SupportIndependent

-- Begin IncidenceCount

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def edgeDegree (G : Graph V E) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => v ∈ G.ends e)).card

omit [Fintype E] [DecidableEq E] in
lemma edgeDegree_sum (G : Graph V E) (F : Finset E) :
    ∑ v, edgeDegree G F v = 2 * F.card := by
  classical
  simp only [edgeDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (e : E) : (∑ v : V, if v ∈ G.ends e then 1 else 0 : ℕ) = 2 := by
    have he : Finset.univ.filter (fun v => v ∈ G.ends e) = (G.ends e).toFinset := by
      ext v
      simp
    rw [←Finset.sum_filter,←Finset.card_eq_sum_ones,he]
    exact Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)
  simp only [hh,Finset.sum_const,smul_eq_mul]
  omega

omit [Fintype V] in
lemma incident_sum_finset (G : Graph V E) (v : V) (F : Finset E) (a : F → ℝ) :
    incidentSum G (∑e : F, a e • Pi.single e.val (1 : ℝ)) v =
      ∑e : F, a e * if v ∈ G.ends e.val then 1 else 0 := by
  change incidentLinear G v _ = _
  rw [map_sum]
  simp only [map_smul,incidentLinear_apply,incident_single,smul_eq_mul]

omit [Fintype V] in
lemma incidence_columns_finset (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (F : Finset E) (R : Finset V)
    (hF : ∀e∈F, 0 < x e)
    (hR : ∀v∈tightVertices G T x, ∀e∈F, v ∈ G.ends e → v ∈ R) :
    LinearIndependent ℝ (fun e : F => incidenceColumn G R e.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let d : E → ℝ := ∑e : F, a e • Pi.single e.val (1 : ℝ)
  have hd : d = 0 := degree_vertex_kernel G T hx (by
    intro e he
    simp only [d,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have hne : j.val ≠ e := by intro h; have := hF j j.property; simp_all
    simp [Ne.symm hne]) (by
    intro v hv ht
    rw [show incidentSum G d v = _ from incident_sum_finset G v F a]
    by_cases hvR : v ∈ R
    · have h := congrFun ha ⟨v,hvR⟩
      simpa [incidenceColumn,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using h
    · apply Finset.sum_eq_zero
      intro e _
      have hn : v ∉ G.ends e.val := fun hm => hvR (hR v (by simp [tightVertices,hv,ht]) e e.property hm)
      simp [hn])
  intro e
  have h := congrFun hd e.val
  simp only [d,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h
  rw [Finset.sum_eq_single e] at h
  · simpa using h
  · intro j _ hj
    have hne : j.val ≠ e.val := fun hh => hj (Subtype.ext hh)
    simp [Ne.symm hne]
  · simp

omit [Fintype V] in
lemma incidence_card_bound (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (F : Finset E) (R : Finset V)
    (hF : ∀e∈F, 0 < x e)
    (hR : ∀v∈tightVertices G T x, ∀e∈F, v ∈ G.ends e → v ∈ R) :
    F.card ≤ R.card := by
  have h := (incidence_columns_finset G T hx F R hF hR).fintype_card_le_finrank
  simpa using h

end ChinesePostman.Polyhedron.Proof
-- End IncidenceCount

-- Begin FractionalDegree

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def fractionalEdges (x : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)

noncomputable def fractionalTight (G : Graph V E) (T : Finset V) (x : E → ℝ) : Finset V :=
  (tightVertices G T x).filter (fun v => ∃e∈fractionalEdges x, v ∈ G.ends e)

omit [Fintype V] in
lemma incident_pair_le (G : Graph V E) {x : E → ℝ} (hx : ∀e, 0 ≤ x e)
    {e f : E} {v : V} (hef : e ≠ f) (he : v ∈ G.ends e) (hf : v ∈ G.ends f) :
    x e + x f ≤ incidentSum G x v := by
  classical
  have hh : ({e,f} : Finset E) ⊆ Finset.univ.filter (fun a => v ∈ G.ends a) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> simp [he,hf]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hh (fun a _ _ => hx a)
  simpa [hef,incidentSum] using h

omit [Fintype V] in
lemma fractional_at_tight (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) {v : V}
    (hv : v ∈ fractionalTight G T x) {f : E} (_hf : 0 < x f) (hfv : v ∈ G.ends f) :
    x f < 1 := by
  classical
  obtain ⟨hvt,e,he,hev⟩ := Finset.mem_filter.mp hv
  have ht : incidentSum G x v = 1 := (Finset.mem_filter.mp hvt).2
  have he' : 0 < x e ∧ x e < 1 := by simpa [fractionalEdges] using he
  by_cases hef : e = f
  · simpa [←hef] using he'.2
  · have hh := incident_pair_le G hx.1.1 hef hev hfv
    rw [ht] at hh
    linarith

omit [Fintype V] in
lemma fractional_degree_ge_two (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) {v : V}
    (hv : v ∈ fractionalTight G T x) : 2 ≤ edgeDegree G (fractionalEdges x) v := by
  classical
  obtain ⟨hvt,e,he,hev⟩ := Finset.mem_filter.mp hv
  have ht : incidentSum G x v = 1 := (Finset.mem_filter.mp hvt).2
  have he' : 0 < x e ∧ x e < 1 := by simpa [fractionalEdges] using he
  have hex : ∃f, f ≠ e ∧ v ∈ G.ends f ∧ 0 < x f := by
    by_contra hn
    push Not at hn
    have hh : incidentSum G x v = x e := by
      unfold incidentSum
      apply Finset.sum_eq_single e
      · intro f hf hfe
        exact le_antisymm (hn f hfe (Finset.mem_filter.mp hf).2) (hx.1.1 f)
      · simp [hev]
    linarith
  obtain ⟨f,hfe,hfv,hf⟩ := hex
  have hfF : f ∈ fractionalEdges x := by
    simp [fractionalEdges,hf,fractional_at_tight G T hx hv hf hfv]
  have hh : ({e,f} : Finset E) ⊆ (fractionalEdges x).filter (fun a => v ∈ G.ends a) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> simp [he,hev,hfF,hfv]
  simpa [edgeDegree,hfe,Ne.symm hfe] using Finset.card_le_card hh

omit [Fintype V] in
lemma fractional_card_bound (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) :
    (fractionalEdges x).card ≤ (fractionalTight G T x).card := by
  apply incidence_card_bound G T hx
  · intro e he
    exact (show 0 < x e ∧ x e < 1 by simpa [fractionalEdges] using he).1
  · intro v hv e he hev
    exact Finset.mem_filter.mpr ⟨hv,e,he,hev⟩

end ChinesePostman.Polyhedron.Proof
-- End FractionalDegree

-- Begin FractionalRegular

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma fractional_degree_exact (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (v : V) :
    edgeDegree G (fractionalEdges x) v = if v ∈ fractionalTight G T x then 2 else 0 := by
  classical
  let R := fractionalTight G T x
  let F := fractionalEdges x
  have hl (v : V) : (if v ∈ R then 2 else 0) ≤ edgeDegree G F v := by
    split_ifs with hv
    · exact fractional_degree_ge_two G T hx hv
    · exact Nat.zero_le _
  have hs : (∑v : V, if v ∈ R then 2 else 0 : ℕ) = 2 * R.card := by
    rw [←Finset.sum_filter]
    simp [mul_comm]
  have hc := fractional_card_bound G T hx
  have he := edgeDegree_sum G F
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hl v)
  have hsum : (∑v : V, if v ∈ R then 2 else 0 : ℕ) = ∑v : V, edgeDegree G F v := by
    rw [hs,he] at *
    dsimp [R,F] at *
    omega
  exact ((Finset.sum_eq_sum_iff_of_le (fun v _ => hl v)).mp hsum v (Finset.mem_univ v)).symm

lemma fractional_endpoint_tight (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) {e : E}
    (he : e ∈ fractionalEdges x) {v : V} (hv : v ∈ G.ends e) :
    v ∈ fractionalTight G T x := by
  classical
  have hp : 0 < edgeDegree G (fractionalEdges x) v := by
    exact Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hv⟩⟩
  rw [fractional_degree_exact G T hx] at hp
  split_ifs at hp with h
  · exact h
  · omega

omit [Fintype V] in
lemma fractional_no_positive_other (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) {v : V}
    (hv : v ∈ fractionalTight G T x) {e : E} (he : v ∈ G.ends e) (hp : 0 < x e) :
    e ∈ fractionalEdges x := by
  classical
  simp [fractionalEdges,hp,fractional_at_tight G T hx hv hp he]

end ChinesePostman.Polyhedron.Proof
-- End FractionalRegular

-- Begin LabelSupportGraph

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def labelGraph (G : Graph V E) (F : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' (F : Set E))

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma labelGraph_adj (G : Graph V E) (F : Finset E) (u v : V) :
    (labelGraph G F).Adj u v ↔ ∃e∈F, G.ends e = s(u,v) := by
  classical
  rw [labelGraph,SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e,he,hh⟩,_⟩
    exact ⟨e,he,hh⟩
  · rintro ⟨e,he,hh⟩
    refine ⟨⟨e,he,hh⟩,?_⟩
    intro h
    apply G.loopless e
    simp [hh,h]

noncomputable def labelNeighborMap (G : Graph V E) (F : Finset E) (v : V) :
    (F.filter (fun e => v ∈ G.ends e)) → (labelGraph G F).neighborSet v := by
  classical
  intro e
  have hv := (Finset.mem_filter.mp e.property).2
  refine ⟨Sym2.Mem.other hv,?_⟩
  apply (labelGraph_adj G F _ _).mpr
  exact ⟨e.val,(Finset.mem_filter.mp e.property).1,(Sym2.other_spec hv).symm⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma labelNeighborMap_bijective (G : Graph V E) (F : Finset E) (v : V)
    (hi : Function.Injective (fun e : F => G.ends e.val)) :
    Function.Bijective (labelNeighborMap G F v) := by
  classical
  constructor
  · intro e f h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    have he := (Finset.mem_filter.mp e.property).2
    have hf := (Finset.mem_filter.mp f.property).2
    have hends : G.ends e.val = G.ends f.val := by
      rw [←Sym2.other_spec he,←Sym2.other_spec hf]
      exact congrArg (fun w => s(v,w)) hh
    exact congrArg (fun a : F => a.val) (hi (a₁ := ⟨e.val,(Finset.mem_filter.mp e.property).1⟩)
      (a₂ := ⟨f.val,(Finset.mem_filter.mp f.property).1⟩) hends)
  · intro w
    obtain ⟨e,he,hends⟩ := (labelGraph_adj G F v w.val).mp w.property
    have hev : v ∈ G.ends e := by simp [hends]
    refine ⟨⟨e,Finset.mem_filter.mpr ⟨he,hev⟩⟩,?_⟩
    apply Subtype.ext
    change Sym2.Mem.other hev = w.val
    have h := (Sym2.other_spec hev).trans hends
    exact (Sym2.eq_iff.mp h).elim (fun h => h.2) (fun h => h.2.trans h.1)

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma labelGraph_degree (G : Graph V E) (F : Finset E) (v : V)
    (hi : Function.Injective (fun e : F => G.ends e.val)) :
    ((labelGraph G F).neighborSet v).ncard = edgeDegree G F v := by
  classical
  have h := Nat.card_congr (Equiv.ofBijective _ (labelNeighborMap_bijective G F v hi))
  rw [Nat.card_coe_set_eq] at h
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,edgeDegree] using h.symm

end ChinesePostman.Polyhedron.Proof
-- End LabelSupportGraph

-- Begin WalkPerturbation

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Graph V E) (F : Finset E)

noncomputable def edgeOfAdj {u v : V} (h : (labelGraph G F).Adj u v) : E :=
  Classical.choose ((labelGraph_adj G F u v).mp h)

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma edgeOfAdj_mem {u v : V} (h : (labelGraph G F).Adj u v) : edgeOfAdj G F h ∈ F :=
  (Classical.choose_spec ((labelGraph_adj G F u v).mp h)).1

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma edgeOfAdj_ends {u v : V} (h : (labelGraph G F).Adj u v) :
    G.ends (edgeOfAdj G F h) = s(u,v) :=
  (Classical.choose_spec ((labelGraph_adj G F u v).mp h)).2

noncomputable def walkPerturb {u v : V} : (labelGraph G F).Walk u v → E → ℝ
  | .nil => 0
  | .cons h p => Pi.single (edgeOfAdj G F h) 1 - walkPerturb p

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma walkPerturb_outside {u v : V} (p : (labelGraph G F).Walk u v) {e : E}
    (he : e ∉ F) : walkPerturb G F p e = 0 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    have hn : e ≠ edgeOfAdj G F h := fun hh => he (hh ▸ edgeOfAdj_mem G F h)
    simp [walkPerturb,hn,ih]

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma walkPerturb_off_edges {u v : V} (p : (labelGraph G F).Walk u v) {e : E}
    (he : G.ends e ∉ p.edges) : walkPerturb G F p e = 0 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    have hn : e ≠ edgeOfAdj G F h := by
      intro hh
      apply he
      simp [hh,edgeOfAdj_ends]
    have hp : G.ends e ∉ p.edges := fun hh => he (by simp [hh])
    simp [walkPerturb,hn,ih hp]

omit [Fintype V] in
lemma incident_walkPerturb {u v : V} (p : (labelGraph G F).Walk u v) (z : V) :
    incidentSum G (walkPerturb G F p) z =
      (if z = u then 1 else 0) - (-1 : ℝ)^p.length * (if z = v then 1 else 0) := by
  induction p with
  | nil => simp [walkPerturb,incidentSum]
  | @cons u w v h p ih =>
    change incidentLinear G z (Pi.single (edgeOfAdj G F h) 1 - walkPerturb G F p) = _
    rw [map_sub]
    simp only [incidentLinear_apply,incident_single,edgeOfAdj_ends,ih,
      SimpleGraph.Walk.length_cons,pow_succ,Sym2.mem_iff]
    have hn : u ≠ w := h.ne
    by_cases hzu : z = u <;> by_cases hzw : z = w <;> by_cases hzv : z = v <;> simp_all

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma walkPerturb_nonzero {u v : V} (p : (labelGraph G F).Walk u v)
    (hp : p.IsTrail) (hn : ¬p.Nil) : walkPerturb G F p ≠ 0 := by
  cases p with
  | nil => exact (hn (by simp)).elim
  | cons h p =>
    have he : s(_,_) ∉ p.edges := (List.nodup_cons.mp hp.edges_nodup).1
    have hz := walkPerturb_off_edges G F p (e := edgeOfAdj G F h) (by simpa [edgeOfAdj_ends] using he)
    intro hh
    have hv := congrFun hh (edgeOfAdj G F h)
    simp [walkPerturb,hz] at hv

omit [Fintype V] in
lemma even_cycle_kernel {u : V} (p : (labelGraph G F).Walk u u)
    (hp : p.IsCycle) (he : Even p.length) :
    ∃d : E → ℝ, d ≠ 0 ∧ (∀e∉F, d e = 0) ∧ ∀v, incidentSum G d v = 0 := by
  refine ⟨walkPerturb G F p,walkPerturb_nonzero G F p hp.isTrail hp.not_nil,
    fun e he => walkPerturb_outside G F p he,?_⟩
  intro v
  rw [incident_walkPerturb,he.neg_one_pow]
  simp

end ChinesePostman.Polyhedron.Proof
-- End WalkPerturbation

-- Begin FractionalCycle

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in
lemma fractional_ends_injective (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) :
    Function.Injective (fun e : fractionalEdges x => G.ends e.val) := by
  classical
  intro e f h
  have he : e.val ∈ positiveEdges x := by
    simpa [positiveEdges] using (show 0 < x e.val ∧ x e.val < 1 by simpa [fractionalEdges] using e.property).1
  have hf : f.val ∈ positiveEdges x := by
    simpa [positiveEdges] using (show 0 < x f.val ∧ x f.val < 1 by simpa [fractionalEdges] using f.property).1
  exact Subtype.ext (congrArg (fun a : positiveEdges x => a.val)
    (positive_ends_injective G T hx (a₁ := ⟨e.val,he⟩) (a₂ := ⟨f.val,hf⟩) h))

lemma fractional_graph_cycles (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) :
    (labelGraph G (fractionalEdges x)).IsCycles := by
  intro v hn
  obtain ⟨w,hw⟩ := hn
  obtain ⟨e,he,hev⟩ := (labelGraph_adj G _ v w).mp hw
  have hv := fractional_endpoint_tight G T hx he (v := v) (by simp [hev])
  rw [labelGraph_degree G _ v (fractional_ends_injective G T hx),fractional_degree_exact G T hx]
  simp [hv]

omit [Fintype V] in
lemma cycle_support_card {H : SimpleGraph V} {u : V} (p : H.Walk u u) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  classical
  have hs : p.support.toFinset = p.support.tail.toFinset := by
    cases p with
    | nil => exact (hp.not_nil (by simp)).elim
    | cons h p => simp [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.end_mem_support]
  rw [hs,List.toFinset_card_of_nodup hp.support_nodup,List.length_tail,SimpleGraph.Walk.length_support]
  omega

lemma fractionalEdges_empty (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (hP : x ∈ CutPoly G T) :
    fractionalEdges x = ∅ := by
  classical
  by_contra hn
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  obtain ⟨u,v,_,hev⟩ := graph_ends_exists G e
  let H := labelGraph G (fractionalEdges x)
  have huv : H.Adj u v := (labelGraph_adj G _ u v).mpr ⟨e,he,hev⟩
  let C := H.connectedComponentMk u
  obtain ⟨p,hp,hverts⟩ := (fractional_graph_cycles G T hx).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C) (v := u) (by rfl) ⟨v,huv⟩
  let S := p.support.toFinset
  have hS (w : V) : w ∈ S ↔ w ∈ C.supp := by
    change w ∈ p.support.toFinset ↔ _
    rw [List.mem_toFinset,←hverts,SimpleGraph.Walk.mem_verts_toSubgraph]
  have hR (w : V) (hw : w ∈ S) : w ∈ fractionalTight G T x := by
    have hwp : w ∈ p.support := List.mem_toFinset.mp hw
    obtain ⟨z,_,hwz⟩ := SimpleGraph.adj_of_mem_walk_support p hp.not_nil hwp
    obtain ⟨a,ha,haw⟩ := (labelGraph_adj G _ w z).mp hwz
    exact fractional_endpoint_tight G T hx ha (by simp [haw])
  have hST : S ⊆ T := by
    intro w hw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hR w hw)).1).1
  have hzero : cutSum G x S = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hcut : Meets G a S := (Finset.mem_filter.mp ha).2
    apply le_antisymm _ (hx.1.1 a)
    by_contra hpos
    have hpos' : 0 < x a := lt_of_not_ge hpos
    obtain ⟨b,c,hab,hb,hc⟩ := hcut
    have haF := fractional_no_positive_other G T hx (hR b hb) (by simp [hab]) hpos'
    have hbc : H.Adj b c := (labelGraph_adj G _ b c).mpr ⟨a,haF,hab⟩
    exact hc ((hS c).mpr (C.mem_supp_of_adj_mem_supp ((hS b).mp hb) hbc))
  have heven : Even S.card := by
    by_contra hh
    have hodd : Odd (S ∩ T).card := by simpa [Finset.inter_eq_left.mpr hST] using Nat.not_even_iff_odd.mp hh
    have hc := hP.2 S hodd
    rw [hzero] at hc
    norm_num at hc
  have hlen : Even p.length := by simpa [S,cycle_support_card p hp] using heven
  obtain ⟨d,hd,hout,hinc⟩ := even_cycle_kernel G (fractionalEdges x) p hp hlen
  apply hd
  apply degree_vertex_kernel G T hx
  · intro a ha
    apply hout
    simp [fractionalEdges,ha]
  · intro w _ _
    exact hinc w

end ChinesePostman.Polyhedron.Proof
-- End FractionalCycle

-- Begin StarParity

namespace ChinesePostman.Polyhedron.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma degree_one_neighbor_unique (H : SimpleGraph V) [DecidableRel H.Adj] {v u w : V}
    (hv : H.degree v = 1) (hu : H.Adj v u) (hw : H.Adj v w) : u = w := by
  obtain ⟨a,_,ha⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  exact (ha u hu).trans (ha w hw).symm

lemma star_parity (H : SimpleGraph V) [DecidableRel H.Adj] (T : Finset V)
    (hleaf : ∀u v, H.Adj u v → (u ∈ T ∧ H.degree u = 1) ∨ (v ∈ T ∧ H.degree v = 1))
    (heven : ∀S : Finset V, (∀u∈S, ∀v, H.Adj u v → v ∈ S) → Even (S ∩ T).card)
    (v : V) : Odd (H.degree v) ↔ v ∈ T := by
  classical
  by_cases hz : H.degree v = 0
  · have hcl : ∀u∈({v}:Finset V), ∀w, H.Adj u w → w ∈ ({v}:Finset V) := by
      intro u hu w huw
      have huv : u = v := by simpa using hu
      subst u
      have hp := (H.degree_pos_iff_exists_adj v).mpr ⟨w,huw⟩
      omega
    have he := heven {v} hcl
    by_cases hv : v ∈ T <;> simp_all
  by_cases ho : H.degree v = 1
  · have hp : 0 < H.degree v := by omega
    obtain ⟨w,hw⟩ := (H.degree_pos_iff_exists_adj v).mp hp
    have hvT : v ∈ T := by
      by_contra hv
      obtain ⟨hwT,hw1⟩ := (hleaf v w hw).resolve_left (fun hh => hv hh.1)
      have hvw := hw.ne
      have hcl : ∀u∈({v,w}:Finset V), ∀z, H.Adj u z → z ∈ ({v,w}:Finset V) := by
        intro u hu z huz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with rfl|rfl
        · have hz := degree_one_neighbor_unique H ho hw huz
          simp [←hz]
        · have hz := degree_one_neighbor_unique H hw1 hw.symm huz
          simp [←hz]
      have he := heven {v,w} hcl
      have hi : ({v,w} ∩ T : Finset V) = {w} := by ext a; simp [hv,hwT]
      rw [hi] at he
      norm_num at he
    simp [ho,hvT]
  have hneighbors : ∀w∈H.neighborFinset v, w ∈ T ∧ H.degree w = 1 := by
    intro w hw
    exact (hleaf v w ((H.mem_neighborFinset v w).mp hw)).resolve_left (fun hh => ho hh.2)
  let S := insert v (H.neighborFinset v)
  have hcl : ∀u∈S, ∀w, H.Adj u w → w ∈ S := by
    intro u hu w huw
    rcases Finset.mem_insert.mp hu with rfl|hu
    · exact Finset.mem_insert_of_mem ((H.mem_neighborFinset u w).mpr huw)
    · have hvu := (H.mem_neighborFinset v u).mp hu
      have hwu := degree_one_neighbor_unique H (hneighbors u hu).2 hvu.symm huw
      exact Finset.mem_insert.mpr (Or.inl hwu.symm)
  have he := heven S hcl
  have hsub : H.neighborFinset v ⊆ T := fun w hw => (hneighbors w hw).1
  have hn : v ∉ H.neighborFinset v := by simp
  by_cases hv : v ∈ T
  · have hi : S ∩ T = insert v (H.neighborFinset v) := by
      simp [S,Finset.insert_inter_of_mem hv,Finset.inter_eq_left.mpr hsub]
    rw [hi,Finset.card_insert_of_notMem hn] at he
    have hodd : Odd (H.degree v) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree] at he
      obtain ⟨k,hk⟩ := he
      exact ⟨k-1,by omega⟩
    simp [hv,hodd]
  · have hi : S ∩ T = H.neighborFinset v := by
      simp [S,Finset.insert_inter_of_notMem hv,Finset.inter_eq_left.mpr hsub]
    rw [hi,SimpleGraph.card_neighborFinset_eq_degree] at he
    simp only [hv,iff_false]
    exact Nat.not_odd_iff_even.mpr he

end ChinesePostman.Polyhedron.Proof
-- End StarParity

-- Begin SingletonVertex

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma singleton_vertex_binary (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (hP : x ∈ CutPoly G T) (e : E) :
    x e = 0 ∨ x e = 1 := by
  classical
  by_cases he : x e = 0
  · exact Or.inl he
  · right
    have hp : 0 < x e := lt_of_le_of_ne (hx.1.1 e) (Ne.symm he)
    have hl := positive_le_one G T hx e
    by_contra hn
    have hf : e ∈ fractionalEdges x := by simp [fractionalEdges,hp,lt_of_le_of_ne hl hn]
    rw [fractionalEdges_empty G T hx hP] at hf
    simp at hf

lemma singleton_vertex_indicator (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (hP : x ∈ CutPoly G T) :
    x = joinVector (positiveEdges x) := by
  classical
  ext e
  rcases singleton_vertex_binary G T hx hP e with h|h <;> simp [joinVector,positiveEdges,h]

omit [Fintype V] in
lemma incident_joinVector (G : Graph V E) (J : Finset E) (v : V) :
    incidentSum G (joinVector J) v = (edgeDegree G J v : ℝ) := by
  classical
  calc
    incidentSum G (joinVector J) v = ∑e : E, if e ∈ J then (if v ∈ G.ends e then (1:ℝ) else 0) else 0 := by
      simp only [incidentSum,joinVector,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> rfl
    _ = ∑e∈J, if v ∈ G.ends e then (1:ℝ) else 0 := by
      rw [←Finset.sum_filter]
      simp
    _ = (edgeDegree G J v : ℝ) := by
      rw [edgeDegree,Finset.card_eq_sum_ones,Nat.cast_sum]
      simp only [Nat.cast_one,Finset.sum_filter]

lemma singleton_vertex_join (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (DegreePoly G T).extremePoints ℝ) (hP : x ∈ CutPoly G T) :
    ∃J, IsJoin G T J ∧ x = joinVector J := by
  classical
  let J := positiveEdges x
  let H := labelGraph G J
  have hxJ : x = joinVector J := singleton_vertex_indicator G T hx hP
  have hdeg (v : V) : H.degree v = edgeDegree G J v := by
    have h := labelGraph_degree G J v (positive_ends_injective G T hx)
    simpa only [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,
      SimpleGraph.card_neighborSet_eq_degree] using h
  have hleaf : ∀u v, H.Adj u v → (u ∈ T ∧ H.degree u = 1) ∨ (v ∈ T ∧ H.degree v = 1) := by
    intro u v huv
    obtain ⟨e,he,hev⟩ := (labelGraph_adj G J u v).mp huv
    have hp : 0 < x e := by simpa [J,positiveEdges] using he
    obtain ⟨a,ha,hae⟩ := positive_has_tight_endpoint G T hx hp
    have haT := (Finset.mem_filter.mp ha).1
    have hat := (Finset.mem_filter.mp ha).2
    have ha1 : H.degree a = 1 := by
      rw [hdeg]
      rw [hxJ,incident_joinVector] at hat
      exact_mod_cast hat
    rw [hev,Sym2.mem_iff] at hae
    rcases hae with rfl|rfl
    · exact Or.inl ⟨haT,ha1⟩
    · exact Or.inr ⟨haT,ha1⟩
  have heven : ∀S : Finset V, (∀u∈S, ∀v, H.Adj u v → v ∈ S) → Even (S ∩ T).card := by
    intro S hS
    have hz : cutSum G x S = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      by_contra hn
      have hp : 0 < x e := lt_of_le_of_ne (hx.1.1 e) (Ne.symm hn)
      have heJ : e ∈ J := by simp [J,positiveEdges,hp]
      obtain ⟨u,v,hev,hu,hv⟩ := (Finset.mem_filter.mp he).2
      exact hv (hS u hu v ((labelGraph_adj G J u v).mpr ⟨e,heJ,hev⟩))
    by_contra hn
    have hh := hP.2 S (Nat.not_even_iff_odd.mp hn)
    rw [hz] at hh
    norm_num at hh
  refine ⟨J,?_,hxJ⟩
  intro v
  have h := star_parity H T hleaf heven v
  simpa only [hdeg,edgeDegree] using h

end ChinesePostman.Polyhedron.Proof
-- End SingletonVertex

-- Begin TightCut

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in
lemma odd_inter_nonempty (S T : Finset V) (hS : Odd (S ∩ T).card) : S.Nonempty := by
  by_contra hn
  have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [he] at hS

omit [DecidableEq E] in
lemma exists_nontrivial_tight_cut (G : Graph V E) (T : Finset V) {x : E → ℝ}
    (hx : x ∈ (CutPoly G T).extremePoints ℝ)
    (hn : x ∉ (DegreePoly G T).extremePoints ℝ) :
    ∃ S : Finset V, Odd (S ∩ T).card ∧ 2 ≤ S.card ∧ 2 ≤ Sᶜ.card ∧ cutSum G x S = 1 := by
  by_contra hno
  push Not at hno
  apply hn
  rw [degreePoly_eq]
  apply mem_extremePoints_of_kernel_zero
  · rw [← degreePoly_eq]
    exact cutPoly_degree G T hx.1
  · intro d hd
    have hz : ∀ e, x e = 0 → d e = 0 := by
      intro e he
      have h := hd (Sum.inl e) (by simp [degreeRows,degreeRhs,he])
      simpa [degreeRows] using h
    have ht : ∀ v ∈ T, incidentSum G x v = 1 → incidentSum G d v = 0 := by
      intro v hv he
      have h := hd (Sum.inr ⟨v,hv⟩) (by simp [degreeRows,degreeRhs,he])
      simpa [degreeRows] using h
    apply cut_vertex_kernel G T hx hz
    intro S hS he
    have hT := cutPoly_total_even G T hx.1
    have hSc : Odd (Sᶜ ∩ T).card := (odd_compl_inter_iff S T hT).mpr hS
    have hsmall (A : Finset V) (hA : Odd (A ∩ T).card) (hc : A.card < 2)
        (he : cutSum G x A = 1) : cutSum G d A = 0 := by
      have hc1 : A.card = 1 := by
        have hp := Finset.card_pos.mpr (odd_inter_nonempty A T hA)
        omega
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc1
      have hv : v ∈ T := by
        by_contra hv
        simp [hv] at hA
      rw [cutSum_singleton] at he ⊢
      exact ht v hv he
    by_cases hc : 2 ≤ S.card
    · by_cases hc' : 2 ≤ Sᶜ.card
      · exact (hno S hS hc hc' he).elim
      · have hh := hsmall Sᶜ hSc (lt_of_not_ge hc') (by simpa only [cutSum_compl] using he)
        simpa only [cutSum_compl] using hh
    · exact hsmall S hS (lt_of_not_ge hc) he

end ChinesePostman.Polyhedron.Proof
-- End TightCut

-- Begin PostmanInduction

namespace ChinesePostman.Polyhedron.Proof

private theorem dominant_card (n : ℕ) :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : Graph V E) (T : Finset V), Fintype.card V = n → CutPoly G T ⊆ dominant G T := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E instV instDV instE instDE G T hcard
    apply cutPoly_subset_dominant_of_extreme G T
    intro x hx
    by_cases hdeg : x ∈ (DegreePoly G T).extremePoints ℝ
    · obtain ⟨J,hJ,hxJ⟩ := singleton_vertex_join G T hdeg hx.1
      refine ⟨x,?_,fun _ => le_rfl⟩
      exact subset_convexHull ℝ _ ⟨J,hJ,hxJ⟩
    · obtain ⟨S,hS,hScard,hSccard,htight⟩ := exists_nontrivial_tight_cut G T hx hdeg
      have hlt : Fintype.card (Option {v // v ∈ S}) < n := by
        rw [← hcard]
        exact collapse_card_lt S hSccard
      have hltc : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        rw [← hcard]
        apply collapse_card_lt Sᶜ
        simpa only [compl_compl] using hScard
      apply glue_dominated_mixtures G S T x hS (cutPoly_total_even G T hx.1) htight
      · exact ih _ hlt _ _ (quotientGraph G (collapseVertex S)) (pushParity T (collapseVertex S)) rfl
          (quotient_cutPoly G T (collapseVertex S) hx.1)
      · exact ih _ hltc _ _ (quotientGraph G (collapseVertex Sᶜ)) (pushParity T (collapseVertex Sᶜ)) rfl
          (quotient_cutPoly G T (collapseVertex Sᶜ) hx.1)

theorem cutPoly_subset_dominant {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (T : Finset V) : CutPoly G T ⊆ dominant G T :=
  dominant_card (Fintype.card V) V E G T rfl

end ChinesePostman.Polyhedron.Proof
-- End PostmanInduction

-- Begin NativeHull

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in
lemma parityPoint_add_even (G : Graph V E) {x : E → ℝ} (hx : x ∈ parityPoints G)
    (e : E) (n : ℕ) : x + (2 * (n:ℝ)) • Pi.single e 1 ∈ parityPoints G := by
  obtain ⟨z,hz,hp,rfl⟩ := hx
  let z' : E → ℤ := fun j => z j + if j = e then 2 * (n:ℤ) else 0
  refine ⟨z',fun j => ?_,fun v => ?_,?_⟩
  · dsimp [z']
    have hj := hz j
    split_ifs <;> positivity
  · have heq : incidentSum G z' v = incidentSum G z v +
        if v ∈ G.ends e then 2 * (n:ℤ) else 0 := by
      simp [incidentSum,z',Finset.sum_add_distrib,Finset.sum_ite_eq']
    rw [heq]
    by_cases h : v ∈ G.ends e
    · simpa only [h,if_true] using (Int.add_modulus_mul_modEq_iff.mpr (hp v) :
        incidentSum G z v + 2 * (n:ℤ) ≡ bParity G v [ZMOD 2])
    · simpa only [h,if_false,add_zero] using hp v
  · ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, z', Int.cast_add]
    by_cases h : j = e <;> simp [h]

omit [Fintype V] in
lemma parityPoint_add_coordinate (G : Graph V E) {x : E → ℝ} (hx : x ∈ parityPoints G)
    (e : E) (r : ℝ) (hr : 0 ≤ r) :
    x + r • Pi.single e 1 ∈ convexHull ℝ (parityPoints G) := by
  obtain ⟨n,hn⟩ := exists_nat_gt r
  have hn0 : 0 < (n:ℝ) := lt_of_le_of_lt hr hn
  let t : ℝ := r / (2 * (n:ℝ))
  have ht0 : 0 ≤ t := div_nonneg hr (by positivity)
  have ht1 : t ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have h := (convex_convexHull ℝ (parityPoints G))
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ (parityPoint_add_even G hx e n))
    (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  convert h using 1
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [t]
  field_simp
  ring

omit [Fintype V] in
lemma parityHull_add_coordinate (G : Graph V E) {x : E → ℝ}
    (hx : x ∈ convexHull ℝ (parityPoints G)) (e : E) (r : ℝ) (hr : 0 ≤ r) :
    x + r • Pi.single e 1 ∈ convexHull ℝ (parityPoints G) := by
  let H := convexHull ℝ (parityPoints G)
  have hc : Convex ℝ {y : E → ℝ | y + r • Pi.single e 1 ∈ H} := by
    intro y hy z hz a b ha hb hab
    have h := (convex_convexHull ℝ (parityPoints G)) hy hz ha hb hab
    change (a • y + b • z) + r • Pi.single e 1 ∈ H
    have heq : (a • y + b • z) + r • Pi.single e 1 =
        a • (y + r • Pi.single e 1) + b • (z + r • Pi.single e 1) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hh := congrArg (fun t : ℝ => t * (r * (Pi.single e (1:ℝ) : E → ℝ) j)) hab
      nlinarith
    rw [heq]
    exact h
  exact convexHull_min (fun y hy => parityPoint_add_coordinate G hy e r hr) hc hx

omit [Fintype V] in
lemma parityHull_upward (G : Graph V E) {x y : E → ℝ}
    (hx : x ∈ convexHull ℝ (parityPoints G)) (hxy : ∀ e, x e ≤ y e) :
    y ∈ convexHull ℝ (parityPoints G) := by
  have h (S : Finset E) : x + ∑ e ∈ S, (y e - x e) • Pi.single e 1 ∈
      convexHull ℝ (parityPoints G) := by
    induction S using Finset.induction_on with
    | empty => simpa using hx
    | @insert e S he ih =>
      have hh := parityHull_add_coordinate G ih e (y e-x e) (sub_nonneg.mpr (hxy e))
      simpa only [Finset.sum_insert he, add_comm, add_left_comm, add_assoc] using hh
  convert h Finset.univ using 1
  ext j
  simp [Pi.single_apply]

end ChinesePostman.Polyhedron.Proof
-- End NativeHull

-- Begin NativeParity

namespace ChinesePostman.Polyhedron.Proof
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def nativeT (G : Graph V E) : Finset V := Finset.univ.filter (fun v => Odd (degree G v))

omit [Fintype V] [DecidableEq E] in
lemma integer_cut_parity (G : Graph V E) (z : E → ℤ)
    (hp : ∀ v, incidentSum G z v ≡ bParity G v [ZMOD 2]) (S : Finset V) :
    cutSum G z S ≡ ((S.filter (fun v => Odd (degree G v))).card : ℤ) [ZMOD 2] := by
  have hs : (∑ v ∈ S, incidentSum G z v) ≡ (∑ v ∈ S, bParity G v) [ZMOD 2] := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih =>
      simpa only [Finset.sum_insert hv] using (hp v).add ih
  have hh := incident_cut_count G z S
  rw [hh] at hs
  simp only [nsmul_eq_mul] at hs
  have hs' : cutSum G z S ≡ ∑ v ∈ S, bParity G v [ZMOD 2] :=
    Int.add_modulus_mul_modEq_iff.mp hs
  have he : (∑ v ∈ S, bParity G v) = ((S.filter (fun v => Odd (degree G v))).card : ℤ) := by
    simp [bParity,Finset.sum_boole]
  rwa [he] at hs'

omit [Fintype V] [DecidableEq E] in
lemma parityPoint_mem_native (G : Graph V E) {x : E → ℝ} (hx : x ∈ parityPoints G) :
    x ∈ postmanPolyhedron G := by
  obtain ⟨z,hz,hp,rfl⟩ := hx
  refine ⟨fun e => by change (0:ℝ) ≤ (z e:ℝ); exact_mod_cast hz e, fun S hS => ?_⟩
  have hm := integer_cut_parity G z hp S
  have ho : ((S.filter (fun v => Odd (degree G v))).card : ℤ) ≡ (1:ℤ) [ZMOD 2] := by
    apply Int.natCast_modEq_iff.mpr
    change (S.filter (fun v => Odd (degree G v))).card % 2 = 1 % 2
    exact Nat.odd_iff.mp hS
  have hc : cutSum G z S ≡ 1 [ZMOD 2] := hm.trans ho
  have hn : 0 ≤ cutSum G z S := Finset.sum_nonneg fun e _ => hz e
  have hne : cutSum G z S ≠ 0 := by
    intro he
    simp [Int.ModEq,he] at hc
  have hle : 1 ≤ cutSum G z S := by omega
  have hcast : ((cutSum G z S : ℤ) : ℝ) = cutSum G (fun e => (z e : ℝ)) S := by
    simp [cutSum]
  rw [← hcast]
  exact_mod_cast hle

omit [DecidableEq E] in
lemma nativePoly_eq_cutPoly (G : Graph V E) : postmanPolyhedron G = CutPoly G (nativeT G) := by
  have he (S : Finset V) : S ∩ nativeT G = S.filter (fun v => Odd (degree G v)) := by
    ext v
    simp [nativeT]
  ext x
  simp only [postmanPolyhedron,CutPoly,IsOddSet,Set.mem_ofPred_eq,he]

lemma joinVector_mem_parityPoints (G : Graph V E) (J : Finset E)
    (hJ : IsJoin G (nativeT G) J) : joinVector J ∈ parityPoints G := by
  let z : E → ℤ := fun e => if e ∈ J then 1 else 0
  refine ⟨z,fun e => by dsimp [z]; split_ifs <;> norm_num,fun v => ?_,?_⟩
  · have he : incidentSum G z v = ((J.filter (fun e => v ∈ G.ends e)).card : ℤ) := by
      have hh := incident_join_nat G J v
      have hh' := congrArg (fun n : ℕ => (n:ℤ)) hh
      simpa [incidentSum,z] using hh'
    rw [he]
    have ho : Odd (J.filter (fun e => v ∈ G.ends e)).card ↔ Odd (degree G v) := by
      simpa only [nativeT,Finset.mem_filter,Finset.mem_univ,true_and] using hJ v
    by_cases hv : Odd (degree G v)
    · simp only [bParity,hv,if_true]
      apply Int.natCast_modEq_iff.mpr
      exact Nat.odd_iff.mp (ho.mpr hv)
    · simp only [bParity,hv,if_false]
      apply Int.natCast_modEq_iff.mpr
      have hh : Even (J.filter (fun e => v ∈ G.ends e)).card := Nat.not_odd_iff_even.mp (fun h => hv (ho.mp h))
      exact Nat.even_iff.mp hh
  · ext e
    simp [joinVector,z]

lemma nativeHull_eq_of_dominant (G : Graph V E)
    (hdom : CutPoly G (nativeT G) ⊆ dominant G (nativeT G)) :
    convexHull ℝ (parityPoints G) = postmanPolyhedron G := by
  apply Set.Subset.antisymm
  · apply convexHull_min (fun _ hx => parityPoint_mem_native G hx)
    rw [nativePoly_eq_cutPoly]
    exact cutPoly_convex G _
  · intro x hx
    rw [nativePoly_eq_cutPoly] at hx
    obtain ⟨y,hy,hyx⟩ := hdom hx
    apply parityHull_upward G (convexHull_mono ?_ hy) hyx
    rintro z ⟨J,hJ,rfl⟩
    exact joinVector_mem_parityPoints G J hJ

end ChinesePostman.Polyhedron.Proof
-- End NativeParity

-- Begin RootAssembly

namespace ChinesePostman.Polyhedron

theorem postman_polyhedron {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (parityPoints G) = postmanPolyhedron G := by
  exact Proof.nativeHull_eq_of_dominant G (Proof.cutPoly_subset_dominant G (Proof.nativeT G))

end ChinesePostman.Polyhedron
-- End RootAssembly

-- Begin Solution

open ChinesePostman.Polyhedron

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) :
    convexHull ℝ (parityPoints G) = postmanPolyhedron G := by
  exact ChinesePostman.Polyhedron.postman_polyhedron G
-- End Solution
