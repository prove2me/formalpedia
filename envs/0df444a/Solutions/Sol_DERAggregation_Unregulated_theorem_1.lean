-- Prove2me | solution 1 for DERAggregation.Unregulated.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T07:54:16.012996+00:00
-- url     : https://prove2.me/submissions/54dda2d7-09f9-40bb-bb45-3fd14e27a964

-- Research directed by Alexander Richard Towell (queelius); Lean proof by OpenAI Codex.
-- Mathematical source: Zuguang Gao, Khaled Alshehri and John R. Birge.
-- Platform definitions/formulation: mikedeng1; statement review: Shuze Chen.
-- Formal foundations: Lean and Mathlib contributors.
import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory DERAggregation.Unregulated
namespace DERResearch
variable {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J] [Fintype L]
variable (M : Market K I J L)
lemma node_sub (x d : I → ℝ) (k : K) : nodeSum M (fun i => x i-d i) k=nodeSum M x k-nodeSum M d k := by
  simp [nodeSum,Finset.sum_sub_distrib]
lemma split_net (z : ℝ) : max z 0-max (-z) 0=z := by
  rcases le_total z 0 with h|h
  · rw [max_eq_right h,max_eq_left (by linarith)];ring
  · rw [max_eq_left h,max_eq_right (by linarith)];ring
lemma box_net {x d : I → ℝ} {y : J → ℝ} (h : BoxA M x d y) : BoxB M (fun i => x i-d i) y := by
  refine ⟨fun i => ⟨?_,?_⟩,h.2.2⟩ <;> linarith [(h.1 i).1,(h.1 i).2,(h.2.1 i).1,(h.2.1 i).2]
lemma box_split (hC : ∀ i,0≤M.C i) {z : I → ℝ} {y : J → ℝ} (h : BoxB M z y) :
    BoxA M (fun i => max (z i) 0) (fun i => max (-z i) 0) y := by
  refine ⟨fun i => ⟨le_max_right _ _,max_le (h.1 i).2 (hC i)⟩,fun i => ⟨le_max_right _ _,?_⟩,h.2⟩
  have hh := split_net (z i)
  linarith [(h.1 i).1]
lemma welfare_net (x d : I → ℝ) (y : J → ℝ) : WA M x d y=WB M (fun i => x i-d i) y := by
  unfold WA WB
  congr 1
  apply Finset.sum_congr rfl
  intro i _;congr 1;ring
lemma welfare_split (z : I → ℝ) (y : J → ℝ) : WA M (fun i => max (z i) 0) (fun i => max (-z i) 0) y=WB M z y := by
  rw [welfare_net];simp_rw [split_net]
lemma feas_net {h : K → ℝ} {x d : I → ℝ} {y : J → ℝ} (hf : FeasA M h x d y) :
    FeasB M h (fun i => x i-d i) y := by
  refine ⟨?_,hf.2.1,hf.2.2.1,box_net M hf.2.2.2⟩
  intro k
  rw [node_sub]
  linarith [hf.1 k]
lemma feas_of_net {h : K → ℝ} {x d : I → ℝ} {y : J → ℝ} (hb : BoxA M x d y)
    (hf : FeasB M h (fun i => x i-d i) y) : FeasA M h x d y := by
  refine ⟨?_,hf.2.1,hf.2.2.1,hb⟩
  intro k
  have hh := hf.1 k
  rw [node_sub] at hh
  linarith
lemma feas_split (hC : ∀ i,0≤M.C i) {h : K → ℝ} {z : I → ℝ} {y : J → ℝ} (hf : FeasB M h z y) :
    FeasA M h (fun i => max (z i) 0) (fun i => max (-z i) 0) y := by
  apply feas_of_net M (box_split M hC hf.2.2.2)
  simpa only [split_net] using hf
lemma opt_net (hC : ∀ i,0≤M.C i) {h : K → ℝ} {x d : I → ℝ} {y : J → ℝ} (ho : IsOptA M h x d y) :
    IsOptB M h (fun i => x i-d i) y := by
  refine ⟨feas_net M ho.1,?_⟩
  intro h' z' y' hf
  have hh := ho.2 h' (fun i => max (z' i) 0) (fun i => max (-z' i) 0) y' (feas_split M hC hf)
  rwa [welfare_split,welfare_net] at hh
lemma opt_of_net {h : K → ℝ} {x d : I → ℝ} {y : J → ℝ} (hb : BoxA M x d y)
    (ho : IsOptB M h (fun i => x i-d i) y) : IsOptA M h x d y := by
  refine ⟨feas_of_net M hb ho.1,?_⟩
  intro h' x' d' y' hf
  rw [welfare_net,welfare_net]
  exact ho.2 h' _ y' (feas_net M hf)
lemma opt_split (hC : ∀ i,0≤M.C i) {h : K → ℝ} {z : I → ℝ} {y : J → ℝ} (ho : IsOptB M h z y) :
    IsOptA M h (fun i => max (z i) 0) (fun i => max (-z i) 0) y := by
  apply opt_of_net M (box_split M hC ho.1.2.2.2)
  simpa only [split_net] using ho
lemma lag_net (lam : K → ℝ) (θ : ℝ) (ν : L → ℝ) (h : K → ℝ) (x d : I → ℝ) (y : J → ℝ) :
    LagA M lam θ ν h x d y=LagB M lam θ ν h (fun i => x i-d i) y := by
  unfold LagA LagB
  rw [welfare_net]
  simp_rw [node_sub]
  congr 3
  apply Finset.sum_congr rfl
  intro k _;ring
lemma lag_split (lam : K → ℝ) (θ : ℝ) (ν : L → ℝ) (h : K → ℝ) (z : I → ℝ) (y : J → ℝ) :
    LagA M lam θ ν h (fun i => max (z i) 0) (fun i => max (-z i) 0) y=LagB M lam θ ν h z y := by
  rw [lag_net];simp_rw [split_net]
lemma mult_net (hC : ∀ i,0≤M.C i) (lam : K → ℝ) (h : K → ℝ) (x d : I → ℝ) (y : J → ℝ) :
    IsMultA M lam h x d y ↔ IsMultB M lam h (fun i => x i-d i) y := by
  constructor
  · rintro ⟨θ,ν,hν,hsl,hmax⟩
    refine ⟨θ,ν,hν,hsl,?_⟩
    intro h' z' y' hb
    have hh := hmax h' (fun i => max (z' i) 0) (fun i => max (-z' i) 0) y' (box_split M hC hb)
    rwa [lag_split,lag_net] at hh
  · rintro ⟨θ,ν,hν,hsl,hmax⟩
    refine ⟨θ,ν,hν,hsl,?_⟩
    intro h' x' d' y' hb
    rw [lag_net,lag_net]
    exact hmax h' _ y' (box_net M hb)
lemma prices (hC : ∀ i,0≤M.C i) (lam : K → ℝ) : IsPriceA M lam ↔ IsPriceB M lam := by
  constructor
  · rintro ⟨h,x,d,y,ho,hm⟩
    exact ⟨h,_,y,opt_net M hC ho,(mult_net M hC lam h x d y).mp hm⟩
  · rintro ⟨h,z,y,ho,hm⟩
    refine ⟨h,(fun i => max (z i) 0),(fun i => max (-z i) 0),y,opt_split M hC ho,?_⟩
    apply (mult_net M hC lam h _ _ y).mpr
    simpa only [split_net] using hm
end DERResearch
namespace DERResearch
variable {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J] [Fintype L]
lemma closed_forall {α β : Type} [TopologicalSpace α] (P : β → α → Prop)
    (h : ∀ b,IsClosed {a | P b a}) : IsClosed {a | ∀ b,P b a} := by
  have he : {a | ∀ b,P b a} = ⋂ b, {a | P b a} := by ext a;simp
  rw [he];exact isClosed_iInter h
variable (M : Market K I J L)
def flow (z : I → ℝ) (y : J → ℝ) (k : K) : ℝ := -nodeSum M z k-genSum M y k
lemma benchmark_exists (h1 : Assumption1 M) (h2 : Assumption2 M) (h3 : ∃ h z y,FeasB M h z y) :
    ∃ h z y,IsOptB M h z y := by
  classical
  let S : Set ((I → ℝ) × (J → ℝ)) := {w | FeasB M (flow M w.1 w.2) w.1 w.2}
  have hflow (k : K) : Continuous (fun w : (I → ℝ) × (J → ℝ) => flow M w.1 w.2 k) := by
    unfold flow nodeSum genSum
    fun_prop
  have hmat (l : L) : Continuous (fun w : (I → ℝ) × (J → ℝ) => Matrix.mulVec M.B (flow M w.1 w.2) l) := by
    unfold Matrix.mulVec dotProduct
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul (hflow k))
  have hclosed : IsClosed S := by
    unfold S FeasB BoxB
    apply IsClosed.inter
    · exact closed_forall _ (fun k => isClosed_eq (hflow k) (hflow k))
    · apply IsClosed.inter
      · exact isClosed_eq (continuous_finset_sum _ (fun k _ => hflow k)) continuous_const
      · apply IsClosed.inter
        · exact closed_forall _ (fun l => isClosed_le (hmat l) continuous_const)
        · apply IsClosed.inter
          · apply closed_forall
            intro i
            change IsClosed ({w : (I → ℝ) × (J → ℝ) | M.C i-M.Z≤w.1 i} ∩ {w | w.1 i≤M.C i})
            exact (isClosed_le continuous_const ((continuous_apply i).comp continuous_fst)).inter
              (isClosed_le ((continuous_apply i).comp continuous_fst) continuous_const)
          · apply closed_forall
            intro j
            change IsClosed ({w : (I → ℝ) × (J → ℝ) | M.ylo j≤w.2 j} ∩ {w | w.2 j≤M.yhi j})
            exact (isClosed_le continuous_const ((continuous_apply j).comp continuous_snd)).inter
              (isClosed_le ((continuous_apply j).comp continuous_snd) continuous_const)
  have hcompact : IsCompact S := by
    apply (isCompact_Icc (a := ((fun i => M.C i-M.Z),M.ylo)) (b := (M.C,M.yhi))).of_isClosed_subset hclosed
    intro w hw
    exact ⟨⟨fun i => (hw.2.2.2.1 i).1,fun j => (hw.2.2.2.2 j).1⟩,
      ⟨fun i => (hw.2.2.2.1 i).2,fun j => (hw.2.2.2.2 j).2⟩⟩
  have hcont : ContinuousOn (fun w : (I → ℝ) × (J → ℝ) => WB M w.1 w.2) S := by
    apply ContinuousOn.sub
    · apply continuousOn_finset_sum
      intro i _
      apply (h1 i).2.2.2.2.1.comp (by fun_prop)
      intro w hw
      exact ⟨by linarith [(hw.2.2.2.1 i).2],by linarith [(hw.2.2.2.1 i).1]⟩
    · apply continuousOn_finset_sum
      intro j _
      apply (h2 j).2.2.2.1.comp (by fun_prop)
      intro w hw
      exact hw.2.2.2.2 j
  have hne : S.Nonempty := by
    obtain ⟨h,z,y,hf⟩ := h3
    have he : h=flow M z y := funext hf.1
    subst h
    exact ⟨(z,y),hf⟩
  obtain ⟨w,hw,hmax⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨flow M w.1 w.2,w.1,w.2,hw,?_⟩
  intro h z y hf
  have he : h=flow M z y := funext hf.1
  subst h
  exact hmax (show (z,y) ∈ S from hf)
end DERResearch
namespace DERResearch
variable {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J] [Fintype L]
variable (M : Market K I J L)
lemma feas_mid {h h' : K → ℝ} {z z' : I → ℝ} {y y' : J → ℝ}
    (hf : FeasB M h z y) (hg : FeasB M h' z' y') :
    FeasB M (fun k => (h k+h' k)/2) (fun i => (z i+z' i)/2) (fun j => (y j+y' j)/2) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k
    simp only [nodeSum,genSum,← Finset.sum_div,Finset.sum_add_distrib]
    have h1 := hf.1 k
    have h2 := hg.1 k
    unfold nodeSum genSum at h1 h2
    linarith
  · rw [← Finset.sum_div,Finset.sum_add_distrib,hf.2.1,hg.2.1];norm_num
  · intro l
    unfold Matrix.mulVec dotProduct
    simp_rw [mul_div,mul_add]
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    have h1 := hf.2.2.1 l
    have h2 := hg.2.2.1 l
    unfold Matrix.mulVec dotProduct at h1 h2
    linarith
  · intro i
    constructor <;> linarith [(hf.2.2.2.1 i).1,(hf.2.2.2.1 i).2,(hg.2.2.2.1 i).1,(hg.2.2.2.1 i).2]
  · intro j
    constructor <;> linarith [(hf.2.2.2.2 j).1,(hf.2.2.2.2 j).2,(hg.2.2.2.2 j).1,(hg.2.2.2.2 j).2]
lemma benchmark_unique (h1 : Assumption1 M) (h2 : Assumption2 M)
    {h h' : K → ℝ} {z z' : I → ℝ} {y y' : J → ℝ}
    (hf : IsOptB M h z y) (hg : IsOptB M h' z' y') : z=z' ∧ y=y' ∧ h=h' := by
  classical
  have hzmem (i : I) : M.C i-z i∈Icc 0 M.Z ∧ M.C i-z' i∈Icc 0 M.Z := by
    constructor <;> constructor <;> linarith [(hf.1.2.2.2.1 i).1,(hf.1.2.2.2.1 i).2,(hg.1.2.2.2.1 i).1,(hg.1.2.2.2.1 i).2]
  have hu (i : I) : (M.u i (M.C i-z i)+M.u i (M.C i-z' i))/2≤M.u i (M.C i-(z i+z' i)/2) := by
    have hh := (h1 i).2.2.2.1.concaveOn.2 (hzmem i).1 (hzmem i).2 (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [show (1/2:ℝ)*(M.C i-z i)+1/2*(M.C i-z' i)=M.C i-(z i+z' i)/2 by ring] at hh
    linarith
  have hc (j : J) : M.c j ((y j+y' j)/2)≤(M.c j (y j)+M.c j (y' j))/2 := by
    have hh := (h2 j).2.2.1.convexOn.2 (hf.1.2.2.2.2 j) (hg.1.2.2.2.2 j) (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [show (1/2:ℝ)*y j+1/2*y' j=(y j+y' j)/2 by ring] at hh
    linarith
  have huSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hu i)
  have hcSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hc j)
  simp only [← Finset.sum_div,Finset.sum_add_distrib] at huSum hcSum
  have hmid := hf.2 _ _ _ (feas_mid M hf.1 hg.1)
  have heq : WB M z y=WB M z' y' := le_antisymm (hg.2 _ _ _ hf.1) (hf.2 _ _ _ hg.1)
  unfold WB at hmid heq
  have hzeq : z=z' := by
    funext i
    by_contra hn
    have hh := (h1 i).2.2.2.1.2 (hzmem i).1 (hzmem i).2 (show M.C i-z i≠M.C i-z' i from fun he => hn (by linarith))
      (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [show (1/2:ℝ)*(M.C i-z i)+1/2*(M.C i-z' i)=M.C i-(z i+z' i)/2 by ring] at hh
    have hs := Finset.sum_lt_sum (s := Finset.univ) (fun k _ => hu k) ⟨i,Finset.mem_univ i,by linarith⟩
    simp only [← Finset.sum_div,Finset.sum_add_distrib] at hs
    linarith
  have hyeq : y=y' := by
    funext j
    by_contra hn
    have hh := (h2 j).2.2.1.2 (hf.1.2.2.2.2 j) (hg.1.2.2.2.2 j) hn
      (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [show (1/2:ℝ)*y j+1/2*y' j=(y j+y' j)/2 by ring] at hh
    have hs := Finset.sum_lt_sum (s := Finset.univ) (fun k _ => hc k) ⟨j,Finset.mem_univ j,by linarith⟩
    simp only [← Finset.sum_div,Finset.sum_add_distrib] at hs
    linarith
  refine ⟨hzeq,hyeq,?_⟩
  funext k
  rw [hf.1.1 k,hg.1.1 k,hzeq,hyeq]
end DERResearch
namespace DERResearch

/-- Theorem 1 (p. 14). Under Assumptions 1–3, with `(h*, z*, y*)` the optimal solution of the
benchmark dispatch (9): the aggregation dispatch (21) has an optimal solution; every optimal
solution of (21) has welfare `W*_A = W*_B` (22), `x − d = z*`, `y = y*`, `h = h*`; the split
`(h*, [z*]⁺, [−z*]⁺, y*)` is optimal for (21); and the wholesale prices (optimal Lagrange
multipliers of (5a)) of the two models coincide. -/
theorem main {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J]
    [Fintype L] (M : Market K I J L) (h1 : Assumption1 M) (h2 : Assumption2 M)
    (h3 : ∃ h z y, FeasB M h z y) :
    ∃ hB zB yB, IsOptB M hB zB yB ∧
      (∃ hA xA dA yA, IsOptA M hA xA dA yA) ∧
      (∀ hA xA dA yA, IsOptA M hA xA dA yA →
        WA M xA dA yA = WB M zB yB ∧ (∀ i, xA i - dA i = zB i) ∧ yA = yB ∧ hA = hB) ∧
      IsOptA M hB (fun i => max (zB i) 0) (fun i => max (-zB i) 0) yB ∧
      (∀ lam : K → ℝ, IsPriceA M lam ↔ IsPriceB M lam) := by
  have hC : ∀ i,0≤M.C i := fun i => (h1 i).1
  obtain ⟨hB,zB,yB,hBopt⟩ := benchmark_exists M h1 h2 h3
  have hs := opt_split M hC hBopt
  refine ⟨hB,zB,yB,hBopt,⟨hB,_,_,yB,hs⟩,?_,hs,prices M hC⟩
  intro hA xA dA yA hAopt
  have hu := benchmark_unique M h1 h2 (opt_net M hC hAopt) hBopt
  refine ⟨?_,fun i => congrFun hu.1 i,hu.2.1,hu.2.2⟩
  rw [welfare_net,hu.1,hu.2.1]


end DERResearch



/-- Theorem 1 (p. 14). Under Assumptions 1–3, with `(h*, z*, y*)` the optimal solution of the
benchmark dispatch (9): the aggregation dispatch (21) has an optimal solution; every optimal
solution of (21) has welfare `W*_A = W*_B` (22), `x − d = z*`, `y = y*`, `h = h*`; the split
`(h*, [z*]⁺, [−z*]⁺, y*)` is optimal for (21); and the wholesale prices (optimal Lagrange
multipliers of (5a)) of the two models coincide. -/
theorem solution {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J]
    [Fintype L] (M : Market K I J L) (h1 : Assumption1 M) (h2 : Assumption2 M)
    (h3 : ∃ h z y, FeasB M h z y) :
    ∃ hB zB yB, IsOptB M hB zB yB ∧
      (∃ hA xA dA yA, IsOptA M hA xA dA yA) ∧
      (∀ hA xA dA yA, IsOptA M hA xA dA yA →
        WA M xA dA yA = WB M zB yB ∧ (∀ i, xA i - dA i = zB i) ∧ yA = yB ∧ hA = hB) ∧
      IsOptA M hB (fun i => max (zB i) 0) (fun i => max (-zB i) 0) yB ∧
      (∀ lam : K → ℝ, IsPriceA M lam ↔ IsPriceB M lam) := by
  exact DERResearch.main M h1 h2 h3


