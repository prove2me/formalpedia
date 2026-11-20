-- Prove2me | solution 1 for DualSepClusterLP.twoPositiveTriangleEndpoints
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T12:41:58.347742+00:00
-- url     : https://prove2.me/submissions/8d578c11-a619-4733-8903-91833de4124e

import Definitions.Def_DualSepClusterLP_TriangleDataPPM0
import Definitions.Def_DualSepClusterLP_TriangleDataPPM1
import Definitions.Def_DualSepClusterLP_TriangleDataPPM2

namespace DualSepClusterLP.TriCert

open Lean.Grind.CommRing

theorem choose_spec (s : Bool) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    isPos (choose s x) = s ∧ choose s x ≤ 4 ∧ OnPiece (choose s x) x := by
  rcases hx with ⟨h0,h1⟩
  cases s <;> by_cases h : x ≤ 1/2 <;> by_cases j : x ≤ 25/26 <;>
    simp only [choose, isPos, OnPiece, h, j, if_true, if_false, Bool.false_eq_true,
      decide_true, decide_false, lo, hi, Set.mem_Icc] <;>
    norm_num at * <;> first | constructor <;> linarith | linarith

section

variable {A : Type} [∀ n : ℕ, OfNat A n] [Add A] [Sub A] [Mul A] [Pow A ℕ]

end

theorem rule_scale (k : ℕ) (hk : k ≤ 4) (x l : ℝ) (hx : OnPiece k x) :
    meanN k (x*l) l = 12*l^2*pivotMean (isPos k) x ∧
    gammaN k (x*l) l = 12*l*pivotGamma (isPos k) x := by
  rcases hx with ⟨hl,hr⟩
  interval_cases k <;> norm_num [lo,hi] at hl hr
  · have h : (13/6:ℝ)*(x-1/2) ≤ 0 := by linarith
    have eq : pivotRescue x = 0 := max_eq_left (le_trans (min_le_right _ _) h)
    constructor <;> norm_num [meanN, gammaN, isPos, pivotMean, pivotGamma, eq] <;> ring
  · have h0 : 0 ≤ (13/6:ℝ)*(x-1/2) := by linarith
    have h1 : (13/6:ℝ)*(x-1/2) ≤ 1 := by linarith
    have eq : pivotRescue x = (13/6)*(x-1/2) := by rw [pivotRescue, min_eq_right h1, max_eq_right h0]
    constructor <;> norm_num [meanN, gammaN, isPos, pivotMean, pivotGamma, eq] <;> ring
  · have h : 1 ≤ (13/6:ℝ)*(x-1/2) := by linarith
    have eq : pivotRescue x = 1 := by rw [pivotRescue, min_eq_left h, max_eq_right (by norm_num)]
    constructor <;> norm_num [meanN, gammaN, isPos, pivotMean, pivotGamma, eq] <;> ring
  · have h : 3/2*x ≤ 2*x-x^2 := by nlinarith [mul_nonneg hl (sub_nonneg.mpr hr)]
    constructor <;> norm_num [meanN, gammaN, isPos, pivotMean, pivotGamma, min_eq_left h] <;> ring
  · have h : 2*x-x^2 ≤ 3/2*x := by nlinarith [mul_nonneg (by linarith : 0 ≤ x) (sub_nonneg.mpr hl)]
    constructor <;> norm_num [meanN, gammaN, isPos, pivotMean, pivotGamma, min_eq_right h] <;> ring

theorem budget_scale (k : ℕ) (x l : ℝ) (h : x ≤ 1) :
    (2773:ℝ)*budgetN k (x*l) l = 1227*l^2*(2-x)*pivotEdgeBudget (isPos k) x := by
  have e : 2-x ≠ 0 := by linarith
  unfold budgetN pivotEdgeBudget
  cases isPos k <;> simp <;> field_simp <;> ring

theorem shape_scale (k : ℕ) (x l : ℝ) :
    shapeN k (x*l) l = l^3*varianceShape (isPos k) x := by
  unfold shapeN varianceShape
  cases isPos k <;> simp <;> ring

theorem onPiece_le_one (k : ℕ) (x : ℝ) (h : OnPiece k x) : x ≤ 1 := by
  refine h.2.trans ?_
  unfold hi
  split
  · norm_num
  · split <;> norm_num

private theorem pivot_abstract (sc : Bool) (x y z t l : ℝ) (m n ga gb fa fb B : ℝ) :
    let cov := (t*l)*l-(x*l)*(y*l)
    let j := (12*l^2*m)*(12*l^2*n)+(12*l*ga)*(12*l*gb)*cov
    let u := (12*l^2*m+12*l^2*n)*(12*l^2)
    let d := (2*l-x*l)*(2*l-y*l)*(2*l-z*l)
    let joint := m*n+ga*gb*(t-x*y)
    25*l^3*(u-j)*(1227*l^2*(2-z)*B)*(2*l-x*l)*(2*l-y*l) -
      25*1227*l^4*(if sc then u-2*j else j)*d -
      2024*144*1227*(l^3*fa)*(l^3*fb)*cov*d =
    (25*144*1227*l^11*(2-x)*(2-y)*(2-z))*
      ((m+n-joint)*B-(if sc then m+n-2*joint else joint)-
      2*(1012/25)*fa*fb*(t-x*y)) := by
  cases sc <;> dsimp <;> ring

theorem pivot_scale (a b c : ℕ) (x y z t l : ℝ) (ha : a ≤ 4) (hb : b ≤ 4)
    (hx : OnPiece a x) (hy : OnPiece b y) (hz : OnPiece c z) :
    pivotN a b c (x*l) (y*l) (z*l) (t*l) l =
    (25*144*1227*l^11*(2-x)*(2-y)*(2-z))*
      triangleSurplus (isPos a) (isPos b) (isPos c) x y z t := by
  obtain ⟨m,g⟩ := rule_scale a ha x l hx
  obtain ⟨n,k⟩ := rule_scale b hb y l hy
  have B := budget_scale c z l (onPiece_le_one c z hz)
  dsimp only [pivotN, triangleSurplus, oppositeSlack]
  rw [m,n,g,k,shape_scale,shape_scale]
  conv_lhs =>
    rw [show ∀ (q r : ℝ), 25*2773*l^3*q*r = 25*l^3*q*(2773*r) by intros; ring, B]
  apply pivot_abstract

theorem triangle_scale (a b c : ℕ) (x y z t l : ℝ) (ha : a ≤ 4) (hb : b ≤ 4)
    (hc : c ≤ 4) (hx : OnPiece a x) (hy : OnPiece b y) (hz : OnPiece c z) :
    homTriangle a b c (x*l) (y*l) (z*l) (t*l) l =
    (25*144*1227*l^11*(2-x)*(2-y)*(2-z))*signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z t := by
  rw [homTriangle, pivot_scale _ _ _ _ _ _ _ _ ha hc hx hz hy,
    pivot_scale _ _ _ _ _ _ _ _ hb ha hy hx hz, pivot_scale _ _ _ _ _ _ _ _ hc hb hz hy hx]
  unfold signedTriangleSurplus
  ring

@[simp] theorem de_add (u v : E) (ctx : Lean.RArray ℝ) :
    (u+v).denote ctx = u.denote ctx + v.denote ctx := rfl

@[simp] theorem de_sub (u v : E) (ctx : Lean.RArray ℝ) :
    (u-v).denote ctx = u.denote ctx - v.denote ctx := rfl

@[simp] theorem de_mul (u v : E) (ctx : Lean.RArray ℝ) :
    (u*v).denote ctx = u.denote ctx * v.denote ctx := rfl

@[simp] theorem de_pow (u : E) (n : ℕ) (ctx : Lean.RArray ℝ) :
    (u^n).denote ctx = u.denote ctx ^ n := rfl

@[simp] theorem de_nat (n : ℕ) (ctx : Lean.RArray ℝ) :
    (OfNat.ofNat n : E).denote ctx = (n : ℝ) := rfl

theorem de_zero (ctx : Lean.RArray ℝ) : (0:E).denote ctx = (0:ℝ) := by
  change ((0:ℕ):ℝ) = _
  norm_num

theorem denote_homTriangle (a b c : ℕ) (x y z t l : E) (ctx : Lean.RArray ℝ) :
    (homTriangle a b c x y z t l).denote ctx =
    homTriangle a b c (x.denote ctx) (y.denote ctx) (z.denote ctx) (t.denote ctx) (l.denote ctx) := by
  have hm (k : ℕ) (v : E) : (meanN k v l).denote ctx = meanN k (v.denote ctx) (l.denote ctx) := by
    match k with
    | 0 | 1 | 2 | 3 | _+4 => simp only [meanN,de_mul,de_pow,de_sub,de_add] <;> rfl
  have hg (k : ℕ) (v : E) : (gammaN k v l).denote ctx = gammaN k (v.denote ctx) (l.denote ctx) := by
    match k with
    | 0 | 1 | _+2 => simp only [gammaN,de_zero,de_mul,de_pow,de_sub,de_add] <;> rfl
  have hs (k : ℕ) (v : E) : (shapeN k v l).denote ctx = shapeN k (v.denote ctx) (l.denote ctx) := by
    unfold shapeN; split <;> first | exact de_zero _ | (simp only [de_mul,de_pow,de_sub,de_add] <;> rfl)
  have hb (k : ℕ) (v : E) : (budgetN k v l).denote ctx = budgetN k (v.denote ctx) (l.denote ctx) := by
    unfold budgetN; split <;> first | exact de_zero _ | (simp only [de_mul,de_pow,de_sub,de_add] <;> rfl)
  have hp (a b c : ℕ) (x y z : E) : (pivotN a b c x y z t l).denote ctx =
      pivotN a b c (x.denote ctx) (y.denote ctx) (z.denote ctx) (t.denote ctx) (l.denote ctx) := by
    dsimp only [pivotN]
    split <;> simp only [de_mul,de_pow,de_sub,de_add,hm,hg,hs,hb] <;> rfl
  simp [homTriangle,hp]

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriGeo

@[simp] theorem eval_add (p q : Form) (x y z : ℝ) :
  (p.add q).eval x y z = p.eval x y z + q.eval x y z := by simp [Form.add,Form.eval]; ring

@[simp] theorem eval_sub (p q : Form) (x y z : ℝ) :
  (p.sub q).eval x y z = p.eval x y z - q.eval x y z := by simp [Form.sub,Form.eval]; ring

@[simp] theorem eval_scale (k : ℤ) (p : Form) (x y z : ℝ) :
  (p.scale k).eval x y z = k*p.eval x y z := by simp [Form.scale, Form.eval]; ring

@[simp] theorem eval_one (x y z : ℝ) : oneF.eval x y z = 1 := by simp [oneF, Form.eval]

@[simp] theorem eval_zero (x y z : ℝ) : zeroF.eval x y z = 0 := by simp [zeroF, Form.eval]

theorem lin_eval (f : Frame) (q : Form) (x y z : ℝ) :
  (f.lin q).eval x y z = q.mix (f.A.eval x y z) (f.B.eval x y z) (f.C.eval x y z) (f.D.eval x y z) := by
  simp [Frame.lin,Form.mix]

theorem useFrame (f : Frame) (s : Tet) (x y z : ℝ) (hf : 0 < f.den) (hs : 0 < s.den)
    (sat : Satisfies (f.requirements s) x y z) (p : ℝ → ℝ → ℝ → Prop) (on : OnTet p s) :
    p x y z := by
  simp only [Satisfies, Frame.requirements, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at sat
  rcases sat with ⟨ha,hb,hc,hd,hm,hM,hx,hX,hy,hY,hz,hZ⟩
  simp [opp] at hM hX hY hZ
  have md := le_antisymm hM hm
  have eqX := le_antisymm hX hx
  have eqY := le_antisymm hY hy
  have eqZ := le_antisymm hZ hz
  have f0 : (0:ℝ) < f.den := by exact_mod_cast hf
  have s0 : (0:ℝ) < s.den := by exact_mod_cast hs
  have mass : (f.A.eval x y z)/f.den+(f.B.eval x y z)/f.den+
      (f.C.eval x y z)/f.den+(f.D.eval x y z)/f.den = 1 := by
    simp [Frame.massDiff] at md
    field_simp; linarith
  have e (u : Form) (v : ℝ) (h : u.mix (f.A.eval x y z) (f.B.eval x y z)
            (f.C.eval x y z) (f.D.eval x y z) = ↑f.den * ↑s.den * v) :
        u.mix (f.A.eval x y z/f.den) (f.B.eval x y z/f.den)
            (f.C.eval x y z/f.den) (f.D.eval x y z/f.den)/s.den = v := by
    simp only [Form.mix] at h ⊢
    field_simp
    linarith
  have X := e s.X x (by simp only [Frame.coordDiff, eval_sub, lin_eval, eval_scale, sub_eq_zero] at eqX; simpa [xF, Form.eval] using eqX)
  have Y := e s.Y y (by simp only [Frame.coordDiff, eval_sub, lin_eval, eval_scale, sub_eq_zero] at eqY; simpa [yF, Form.eval] using eqY)
  have Z := e s.Z z (by simp only [Frame.coordDiff, eval_sub, lin_eval, eval_scale, sub_eq_zero] at eqZ; simpa [zF, Form.eval] using eqZ)
  simpa only [X,Y,Z] using on _ _ _ _ (div_nonneg ha f0.le) (div_nonneg hb f0.le)
      (div_nonneg hc f0.le) (div_nonneg hd f0.le) mass

theorem combination_valid {cs : List Form} {x y z : ℝ} (sat : Satisfies cs x y z) (w : List Coeff) :
    0 ≤ (combination cs w).eval x y z := by
  induction w with
  | nil => simp [combination]
  | cons v vs ih =>
    obtain ⟨i,k⟩ := v
    simp only [combination, eval_add, eval_scale, Int.cast_natCast]
    apply add_nonneg _ ih
    apply mul_nonneg (by positivity)
    cases h : cs[i]? with
    | none => simp
    | some q =>
      simpa using sat q (List.mem_of_getElem? h)

theorem derive {cs : List Form} {q : Form} {p : Derivation}
    (h : p.valid cs q = true) {x y z : ℝ} (sat : Satisfies cs x y z) :
    0 ≤ q.eval x y z := by
  obtain ⟨hm,id⟩ := of_decide_eq_true h
  have h' := combination_valid sat p.terms
  rw [← id, eval_scale] at h'
  have hp : (0:ℝ) < (p.mul:ℕ) := by exact_mod_cast hm
  simpa using nonneg_of_mul_nonneg_right h' (show (0:ℝ) < ((p.mul:ℕ):ℤ) by exact_mod_cast hm)

theorem allDerivable_valid (cs : List Form) (qs : List Form) (ps : List Derivation)
    (h : allDerivable cs qs ps = true) {x y z : ℝ} (sat : Satisfies cs x y z) : Satisfies qs x y z := by
  induction qs generalizing ps with
  | nil => simp [Satisfies]
  | cons q qs ih =>
    cases ps with
    | nil => simp [allDerivable] at h
    | cons p ps =>
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hv
      · exact derive a sat
      · exact ih _ b _ hv

theorem Cover.sound {tiles : Array Tile} {p : ℝ → ℝ → ℝ → Prop}
    (on : ∀ i : Fin tiles.size, OnTet p tiles[i].1) (tree : Cover) (cs : List Form)
    (ok : tree.check tiles cs = true) (x y z : ℝ) (sat : Satisfies cs x y z) : p x y z := by
  induction tree generalizing cs with
  | empty pr =>
    have := derive ok sat
    norm_num [opp] at this
  | leaf idx proofs =>
    unfold check at ok
    split at ok
    · contradiction
    next t eq =>
      obtain ⟨ht,hc⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨h₁,h₂⟩ := of_decide_eq_true ht
      have hi := (Array.getElem?_eq_some_iff.mp eq)
      obtain ⟨bound,eq'⟩ := hi
      exact useFrame _ _ x y z h₂ h₁ (allDerivable_valid _ _ proofs hc sat) _ (by simpa [eq'] using on ⟨idx,bound⟩)
  | cut q pos neg ih₁ ih₂ =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ok
    rcases le_total 0 (q.eval x y z) with h|h
    · apply ih₁ _ a
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact h
      · exact sat f hf
    · apply ih₂ _ b
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [opp] using h
      · exact sat f hf

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriGeo

theorem region_endpoints (P : ℝ → Prop) (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : tripleLower x y z ≤ tripleUpper x y z)
    (lA : InRegion 0 x y z → P 0) (lB : InRegion 1 x y z → P 0)
    (l01 : InRegion 2 x y z → P (x+y-1))
    (l02 : InRegion 3 x y z → P (x+z-1))
    (l12 : InRegion 4 x y z → P (y+z-1))
    (u0 : InRegion 5 x y z → P x)
    (u1 : InRegion 6 x y z → P y)
    (u2 : InRegion 7 x y z → P z) : P (tripleLower x y z) ∧ P (tripleUpper x y z) := by
  have hfeas : x+y-z ≤ 1 ∧ x+z-y ≤ 1 ∧ y+z-x ≤ 1 := by
    have A : x+y-1 ≤ tripleLower x y z := (le_max_left _ _).trans (le_max_right _ _)
    have B : y+z-1 ≤ tripleLower x y z := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    have C : z+x-1 ≤ tripleLower x y z := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    have X : tripleUpper x y z ≤ x := min_le_left _ _
    have Y : tripleUpper x y z ≤ y := (min_le_right _ _).trans (min_le_left _ _)
    have Z : tripleUpper x y z ≤ z := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith,by linarith,by linarith⟩
  obtain ⟨h01,h02,h12⟩ := hfeas
  have casesMin : (x ≤ y ∧ x ≤ z) ∨ (y ≤ x ∧ y ≤ z) ∨ (z ≤ x ∧ z ≤ y) := by
    by_cases h' : x ≤ y
    · rcases le_total x z with u|u
      · exact Or.inl ⟨h',u⟩
      · exact Or.inr (Or.inr ⟨u,u.trans h'⟩)
    · rcases le_total y z with u|u
      · exact Or.inr (Or.inl ⟨le_of_not_ge h',u⟩)
      · exact Or.inr (Or.inr ⟨u.trans (le_of_not_ge h'),u⟩)
  constructor
  · by_cases hzero : x+y ≤ 1 ∧ x+z ≤ 1 ∧ y+z ≤ 1
    · obtain ⟨a,b,c⟩ := hzero
      have lower : tripleLower x y z = 0 := by
        unfold tripleLower
        apply max_eq_left
        simp only [max_le_iff]
        exact ⟨by linarith,by linarith,by linarith⟩
      rw [lower]
      rcases le_total (x+y+z) 1 with cut|cut
      · exact lA ⟨hx,hy,hz,cut⟩
      · exact lB ⟨cut,a,b,c⟩
    · rcases casesMin with ⟨A,B⟩ | ⟨A,B⟩ | ⟨A,B⟩
      · have hsum : 1 ≤ y+z := by by_contra! hh; exact hzero ⟨by linarith,by linarith,by linarith⟩
        have lower : tripleLower x y z = y+z-1 := by
          simp only [tripleLower, max_eq_left (show z+x-1 ≤ y+z-1 by linarith),
            max_eq_right (show x+y-1 ≤ y+z-1 by linarith),max_eq_right (show 0 ≤ y+z-1 by linarith)]
        rw [lower]
        exact l12 ⟨hsum,A,B,h12⟩
      · have hsum : 1 ≤ x+z := by by_contra! hh; exact hzero ⟨by linarith,by linarith,by linarith⟩
        have lower : tripleLower x y z = x+z-1 := by
          rw [tripleLower,max_eq_right (show y+z-1 ≤ z+x-1 by linarith),
            max_eq_right (show x+y-1 ≤ z+x-1 by linarith),max_eq_right (show 0 ≤ z+x-1 by linarith)]
          ring
        rw [lower]
        exact l02 ⟨hsum,A,B,h02⟩
      · have hsum : 1 ≤ x+y := by by_contra! hh; exact hzero ⟨by linarith,by linarith,by linarith⟩
        have lower : tripleLower x y z = x+y-1 := by
          rw [tripleLower, max_eq_left (show max (y+z-1) (z+x-1) ≤ x+y-1 from max_le (by linarith) (by linarith)),
            max_eq_right (show 0 ≤ x+y-1 by linarith)]
        rw [lower]
        exact l01 ⟨hsum,A,B,h01⟩
  · rcases casesMin with ⟨A,B⟩ | ⟨A,B⟩ | ⟨A,B⟩
    · rw [tripleUpper, min_eq_left (le_min A B)]
      exact u0 ⟨hx,A,B,h12⟩
    · rw [tripleUpper, min_eq_left B,min_eq_right A]
      exact u1 ⟨hy,A,B,h02⟩
    · rw [tripleUpper, min_eq_right B,min_eq_right A]
      exact u2 ⟨hz,A,B,h01⟩

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriGeo

open TriCert

theorem satAxisX (k : ℕ) (x y z : ℝ) (hk : k ≤ 4) (h : OnPiece k x) : Satisfies (AxisX k) x y z := by
  obtain ⟨ha,hb⟩ := h
  interval_cases k <;> norm_num [lo,hi] at ha hb <;>
    simp only [Satisfies,AxisX, List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;>
    norm_num [Form.eval] <;> (repeat' apply And.intro) <;> linarith only [ha,hb]

theorem satAxisY (k : ℕ) (x y z : ℝ) (hk : k ≤ 4) (h : OnPiece k y) : Satisfies (AxisY k) x y z := by
  obtain ⟨ha,hb⟩ := h
  interval_cases k <;> norm_num [lo,hi] at ha hb <;>
    simp only [Satisfies,AxisY, List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;>
    norm_num [Form.eval] <;> (repeat' apply And.intro) <;> linarith only [ha,hb]

theorem satAxisZ (k : ℕ) (x y z : ℝ) (hk : k ≤ 4) (h : OnPiece k z) : Satisfies (AxisZ k) x y z := by
  obtain ⟨ha,hb⟩ := h
  interval_cases k <;> norm_num [lo,hi] at ha hb <;>
    simp only [Satisfies,AxisZ, List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;>
    norm_num [Form.eval] <;> (repeat' apply And.intro) <;> linarith only [ha,hb]

theorem regionForms_sat (e : ℕ) (he : e ≤ 7) (x y z : ℝ) (h : InRegion e x y z) : Satisfies (RegionForms e) x y z := by
  interval_cases e <;> obtain ⟨h0,h1,h2,h3⟩ := h <;>
    simp only [Satisfies,RegionForms, List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;>
    norm_num [Form.eval] <;> (repeat' apply And.intro) <;> linarith only [h0,h1,h2,h3]

theorem allForms_sat (a b c e : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hc : c ≤ 4) (he : e ≤ 7)
  (x y z : ℝ) (hx : OnPiece a x) (hy : OnPiece b y) (hz : OnPiece c z)
  (h : InRegion e x y z) : Satisfies (AllForms a b c e) x y z := by
  have A := satAxisX a x y z ha hx
  have B := satAxisY b x y z hb hy
  have C := satAxisZ c x y z hc hz
  have E := regionForms_sat e he x y z h
  intro q hq
  simp only [AllForms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (((hr|hz)|hy)|hx)|rfl
  · exact E q hr
  · exact C q hz
  · exact B q hy
  · exact A q hx
  · simp

theorem onPiece_zero (a : ℕ) (x : ℝ) (hx : OnPiece a x) : 0 ≤ x := by
  apply le_trans _ hx.1
  unfold lo
  split
  · norm_num
  · split <;> norm_num

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TrianglePacking

theorem slot_injective {a b c i j k : Nat} (h : a+b+c ≤ 11) (h' : i+j+k ≤ 11)
    (e : slot a b c = slot i j k) : a=i ∧ b=j ∧ c=k := by
  unfold slot at e
  have deltaLo : -11 ≤ (c : Int) - k := by omega
  have deltaHi : (c : Int) - k ≤ 11 := by omega
  have rel : ((a:Int)-i) + 67*((b:Int)-j) + 79*((c:Int)-k)=0 := by omega
  have lo : -11 ≤ (a:Int)-i := by omega
  have hi : (a:Int)-i ≤ 11 := by omega
  generalize ha : (a:Int)-i = aa at *
  generalize hb : (b:Int)-j = bb at *
  generalize hw : (c : Int) - k = w at *
  interval_cases w <;> omega

theorem slot_le {a b c : Nat} (h : a+b+c ≤ 11) : slot a b c ≤ 869 := by
  unfold slot
  omega

theorem weighted_eq (a : Fin 4 → ℕ) :
    ∑ i, a i * weight i = slot (a 1) (a 2) (a 3) := by
  simp [Fin.sum_univ_succ, weight, slot, Nat.mul_comm, Nat.add_assoc]

theorem weighted_injective {a b : Fin 4 → ℕ} (ha : ∑ i, a i = 11)
    (hb : ∑ i, b i = 11)
    (h : ∑ i, a i * weight i = ∑ i, b i * weight i) : a = b := by
  simp [Fin.sum_univ_succ] at ha hb
  change a 0 + (a 1 + (a 2 + a 3)) = 11 at ha
  change b 0 + (b 1 + (b 2 + b 3)) = 11 at hb
  simp only [weighted_eq] at h
  obtain ⟨h1,h2,h3⟩ := slot_injective (a:=a 1) (b:=a 2) (c:=a 3)
    (i:=b 1) (j:=b 2) (k:=b 3) (by omega) (by omega) h
  have h0 : a 0=b 0 := by omega
  funext i
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3

theorem weighted_le {a : Fin 4 → ℕ} (ha : ∑ i, a i ≤ 11) :
    ∑ i, a i * weight i ≤ 869 := by
  simp [Fin.sum_univ_succ] at ha
  rw [weighted_eq]
  apply slot_le
  omega

end DualSepClusterLP.TrianglePacking

namespace DualSepClusterLP.TriBern

private theorem guardMask_sum (k n : ℕ) :
    guardMask k n = 2^k * ∑ i ∈ Finset.range n, (2^(k+1):ℕ)^i := by
  have hb : 2 ≤ 2^(k+1) := by rw [pow_succ]; have := Nat.two_pow_pos k; omega
  rw [guardMask, Nat.geomSum_eq hb, Nat.pow_mul]

private theorem guardMask_succ (k n : ℕ) : guardMask k (n+1) =
    2^k + 2^(k+1) * guardMask k n := by
  rw [guardMask_sum, guardMask_sum, Finset.sum_range_succ']
  simp only [pow_zero, pow_succ', ← Finset.mul_sum]
  ring

private theorem guardMask_bit {k n i : ℕ} (hi : i < n) :
    (guardMask k n).testBit (k+(k+1)*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [guardMask_succ]
    have h : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      have hh := Nat.testBit_mod_two_pow (2^k + 2^(k+1) * guardMask k n) (k+1) k
      simpa [Nat.testBit_two_pow, Nat.mod_eq_of_lt h] using hh.symm
    | succ i =>
      rw [show k + (k+1)*(i+1) = (k+(k+1)*i) + (k+1) by ring,
          ← Nat.testBit_div_two_pow]
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h, Nat.zero_add]
      exact ih (by omega)

theorem clearGuards {k n y : ℕ} (h : y &&& guardMask k n = 0) (i : ℕ) (hi : i < n) :
    y.testBit (k+(k+1)*i) = false := by
  have hh := congrArg (fun t : ℕ => t.testBit (k+(k+1)*i)) h
  simpa [guardMask_bit hi, Nat.testBit_and] using hh

private theorem topBit_small {k y : ℕ} (h : y.testBit k = false) : y % 2^(k+1) < 2^k := by
  by_contra! hlarge
  have hy := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hlarge
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  simp [Nat.testBit_mod_two_pow, h] at hy

theorem digits_nonnegative (k n : ℕ) (a : ℕ → ℤ) (y : ℕ)
    (repr : (y : ℤ) = ∑ i ∈ Finset.range n, a i * (2^(k+1):ℤ)^i)
    (bound : ∀ i < n, |a i| < (2:ℤ)^k)
    (guard : ∀ i < n, y.testBit (k+(k+1)*i) = false) :
    ∀ i < n, 0 ≤ a i := by
  induction n generalizing a y with
  | zero => simp
  | succ n ih =>
    let b : ℤ := 2^(k+1)
    have hb : 0 < b := by dsimp [b]; positivity
    let rest : ℤ := ∑ i ∈ Finset.range n, a (i+1) * b^i
    have hy : (y : ℤ) = a 0 + b*rest := by
      rw [Finset.sum_range_succ'] at repr
      simpa [rest,b,pow_succ',mul_left_comm,mul_assoc,← Finset.mul_sum,add_comm] using repr
    have yd := topBit_small (k:=k) (y:=y) (by simpa using guard 0 (by omega))
    have b0 := bound 0 (by omega)
    rw [abs_lt] at b0
    have modEq : (y:ℤ)%b = a 0 % b := by rw [hy]; simp
    have ym : (↑(y%(2^(k+1))) : ℤ) = (y:ℤ) % b := by norm_cast
    have yd' : (y:ℤ)%b < 2^k := by rw [←ym]; exact_mod_cast yd
    have bsplit : b = 2^k+2^k := by dsimp [b]; ring
    have h0 : 0 ≤ a 0 := by
      by_contra! hneg
      have mm : a 0 % b = a 0 + b := by
        calc
          _ = (a 0+b)%b := by simp
          _ = _ := Int.emod_eq_of_lt (by omega) (by omega)
      omega
    have hlt : a 0 < b := by omega
    intro i hi
    cases i with
    | zero => exact h0
    | succ i =>
      let q := y / 2^(k+1)
      have hq : (q : ℤ) = rest := by
        change ((y / 2^(k+1):ℕ):ℤ) = rest
        rw [Int.natCast_ediv]
        change (y:ℤ) / b = rest
        rw [hy, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt h0 hlt, zero_add]
      apply ih (fun j => a (j+1)) q hq (fun j hj => bound (j+1) (by omega)) _ i (by omega)
      intro j hj
      dsimp [q]
      rw [Nat.testBit_div_two_pow]
      simpa only [show k+(k+1)*j+(k+1) = k+(k+1)*(j+1) by ring] using
        guard (j+1) (by omega)

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open MvPolynomial

open DualSepClusterLP.TrianglePacking

private theorem homogeneous_degree {p : Poly4} (hp : p.IsHomogeneous 11)
    {e : Exp4} (he : e ∈ p.support) : ∑ i, e i = 11 := by
  have h := hp (MvPolynomial.mem_support_iff.mp he)
  simpa [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using h

private theorem code_inj {p : Poly4} (hp : p.IsHomogeneous 11)
    {e f : Exp4} (he : e ∈ p.support) (hf : f ∈ p.support) (h : code e = code f) : e = f := by
  apply DFunLike.coe_injective
  apply weighted_injective (homogeneous_degree hp he) (homogeneous_degree hp hf) h

private noncomputable def bucket (p : Poly4) (i : ℕ) : ℤ := by
  classical
  exact if h : ∃ e ∈ p.support, code e = i then p.coeff h.choose else 0

private theorem bucket_at {p : Poly4} (hp : p.IsHomogeneous 11) {e : Exp4}
    (he : e ∈ p.support) : bucket p (code e) = p.coeff e := by
  classical
  have h : ∃ f ∈ p.support, code f = code e := ⟨e,he,rfl⟩
  rw [bucket, dif_pos h, code_inj hp h.choose_spec.1 he h.choose_spec.2]

private theorem eval_flat (p : Poly4) (hp : p.IsHomogeneous 11) (b : ℤ) :
    p.eval (fun i => b ^ weight i) =
    ∑ j ∈ Finset.range 870, bucket p j * b^j := by
  classical
  have hsub : p.support.image code ⊆ Finset.range 870 := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <| weighted_le (homogeneous_degree hp he).le
  rw [MvPolynomial.eval_eq']
  calc
    _ = ∑ e ∈ p.support, bucket p (code e) * b^(code e) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [bucket_at hp he]
      congr 1
      simp [code, pow_mul, Nat.mul_comm, ← Finset.prod_pow_eq_pow_sum]
    _ = ∑ j ∈ p.support.image code, bucket p j * b^j := by
      rw [Finset.sum_image]
      intro a ha b hb h
      exact code_inj hp ha hb h
    _ = _ := by
      apply Finset.sum_subset hsub
      intro i _ hi
      have hh : ¬ ∃ e ∈ p.support, code e=i := by simpa using hi
      rw [bucket, dif_neg hh, zero_mul]

theorem packedPoly_sound (p : Poly4) (hp : p.IsHomogeneous 11) (k : ℕ)
    (hc : ∀ e ∈ p.support, |p.coeff e| < (2:ℤ)^k)
    (y : ℤ) (hy : y = p.eval (fun i => (2^(k+1):ℤ)^weight i))
    (hy0 : 0 ≤ y) (guard : y.toNat &&& guardMask k 870 = 0)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ p.eval₂ (Int.castRingHom ℝ) w := by
  have hre := hy.trans (eval_flat p hp _)
  have hr : (y.toNat : ℤ) = ∑ i ∈ Finset.range 870, bucket p i * (2^(k+1):ℤ)^i :=
    (Int.toNat_of_nonneg hy0).trans hre
  have hb : ∀ j < 870, |bucket p j| < (2:ℤ)^k := by
    intro j _
    classical
    unfold bucket
    split
    next h => exact hc _ h.choose_spec.1
    next => simp
  have hn := digits_nonnegative k 870 (bucket p) _ hr hb (clearGuards guard)
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_nonneg
  intro e he
  apply mul_nonneg _ (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)
  have hs := hn (code e) (Nat.lt_succ_of_le <| weighted_le (homogeneous_degree hp he).le)
  rw [bucket_at hp he] at hs
  change (0:ℝ) ≤ (p.coeff e : ℤ)
  exact_mod_cast hs

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TrianglePacking

open MvPolynomial

private noncomputable def lift : NP →+* ZP := MvPolynomial.map (Nat.castRingHom ℤ)

private noncomputable def size : NP →+* ℕ := MvPolynomial.eval (fun _ => 1)

private def Bounded (p : ZP) (n : ℕ) : Prop :=
  ∃ q r : NP, p = lift q - lift r ∧ size q + size r = n

private theorem bounded_int (z : ℤ) : Bounded (C z) z.natAbs := by
  cases z with
  | ofNat n => exact ⟨C n,0,by simp [lift],by simp [size]⟩
  | negSucc n =>
    refine ⟨0,C (n+1),?_,by simp [size]⟩
    simp [lift,Int.negSucc_eq]

private theorem bounded_x (i : Fin 4) : Bounded (X i) 1 :=
  ⟨X i, 0, by simp [lift], by simp [size]⟩

private theorem bounded_neg {p : ZP} {n : ℕ} (h : Bounded p n) : Bounded (-p) n := by
  obtain ⟨a,b, rfl,h⟩ := h
  exact ⟨b,a,by abel,by omega⟩

private theorem bounded_add {p q : ZP} {m n : ℕ} (h : Bounded p m) (k : Bounded q n) :
    Bounded (p+q) (m+n) := by
  obtain ⟨a,b,rfl,rfl⟩ := h
  obtain ⟨c,d,rfl,rfl⟩ := k
  exact ⟨a+c,b+d,by simp only [map_add]; abel, by simp only [map_add]; omega⟩

private theorem bounded_mul {p q : ZP} {m n : ℕ} (h : Bounded p m) (k : Bounded q n) :
    Bounded (p*q) (m*n) := by
  obtain ⟨a,b,rfl,rfl⟩ := h
  obtain ⟨c,d,rfl,rfl⟩ := k
  exact ⟨a*c+b*d,a*d+b*c,by simp only [map_add,map_mul];ring,
    by simp only [map_add,map_mul]; ring⟩

private theorem bounded_pow {p : ZP} {m : ℕ} (h : Bounded p m) (k : ℕ) :
    Bounded (p^k) (m^k) := by
  induction k with
  | zero => simpa using bounded_int 1
  | succ k ih => simpa only [pow_succ] using bounded_mul ih h

private theorem bounded_expr (e : PE) : Bounded (toMv e) (bound e) := by
  induction e with
  | num z | intCast z => exact bounded_int z
  | natCast n => exact bounded_int n
  | var i => exact bounded_x _
  | neg a ha => exact bounded_neg ha
  | add a b ha hb => exact bounded_add ha hb
  | sub a b ha hb =>
    change Bounded (toMv a - toMv b) (bound a+bound b)
    rw [sub_eq_add_neg]
    exact bounded_add ha (bounded_neg hb)
  | mul a b ha hb => exact bounded_mul ha hb
  | pow a k h => exact bounded_pow h k

private theorem coeff_le_size (p : NP) (m : Fin 4 →₀ ℕ) : p.coeff m ≤ size p := by
  classical
  simp [size,eval_eq]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le (p.coeff i)) hm
  · simp [MvPolynomial.notMem_support_iff.mp hm]

theorem coeff_bound (e : PE) (m : Fin 4 →₀ ℕ) : |(toMv e).coeff m| ≤ (bound e : ℤ) := by
  obtain ⟨q,r,h,k⟩ := bounded_expr e
  rw [h,← k,MvPolynomial.coeff_sub]
  simp only [lift,MvPolynomial.coeff_map,Nat.cast_add]
  have hq := coeff_le_size q m
  have hr := coeff_le_size r m
  change |((q.coeff m : ℕ) : ℤ) - ((r.coeff m : ℕ) : ℤ)| ≤ (size q : ℤ) + (size r : ℤ)
  exact abs_le.mpr (by omega)

private def G.Spec (p : ZP) : G → Prop
  | .bad => True
  | .zero => p=0
  | .deg n => p.IsHomogeneous n

private theorem spec_const (z : ℤ) : G.Spec (C z) (if z=0 then .zero else .deg 0) := by
  by_cases h : z=0
  · simp [h,G.Spec]
  · simpa [h,G.Spec] using isHomogeneous_C (Fin 4) z

private theorem spec_neg {p : ZP} {a : G} (h : a.Spec p) : a.Spec (-p) := by
  cases a with
  | bad => trivial
  | zero => simp_all [G.Spec]
  | deg m => exact IsHomogeneous.neg h

private theorem spec_add {p q : ZP} {a b : G} (h : a.Spec p) (k : b.Spec q) :
    (a.plus b).Spec (p+q) := by
  cases a with
  | bad => cases b <;> trivial
  | zero =>
    change p=0 at h
    subst p
    simpa [G.plus] using k
  | deg n =>
    cases b with
    | bad => trivial
    | zero =>
      change q=0 at k
      subst q
      simpa [G.plus] using h
    | deg m =>
      by_cases hh : n=m
      · subst m
        simpa [G.plus,G.Spec] using (MvPolynomial.IsHomogeneous.add h k)
      · simp [G.plus,hh,G.Spec]

private theorem spec_mul {p q : ZP} {a b : G} (h : a.Spec p) (k : b.Spec q) :
    (a.times b).Spec (p*q) := by
  cases a <;> cases b <;> simp_all [G.times,G.Spec]
  exact IsHomogeneous.mul h k

private theorem spec_pow {p : ZP} {a : G} (h : a.Spec p) (k : ℕ) :
    (a.power k).Spec (p^k) := by
  by_cases hh : k=0
  · subst k; simp [G.power,G.Spec,MvPolynomial.isHomogeneous_one]
  · cases a <;> simp_all [G.power,G.Spec]
    exact IsHomogeneous.pow h _

private theorem spec_expr (e : PE) : (grade e).Spec (toMv e) := by
  induction e with
  | num z | intCast z => exact spec_const z
  | natCast n => simpa [grade,toMv] using spec_const (n:ℤ)
  | var i => exact isHomogeneous_X ℤ _
  | neg a ha => exact spec_neg ha
  | add a b ha hb => exact spec_add ha hb
  | sub a b ha hb =>
    change ((grade a).plus (grade b)).Spec (toMv a-toMv b)
    rw [sub_eq_add_neg]
    exact spec_add ha (spec_neg hb)
  | mul a b ha hb => exact spec_mul ha hb
  | pow a k ha => exact spec_pow ha k

theorem isHomogeneous_of_grade (e : PE) (d : ℕ) (h : grade e = .zero ∨ grade e = .deg d) :
    (toMv e).IsHomogeneous d := by
  have he := spec_expr e
  rcases h with h|h <;> rw [h] at he
  · rw [show toMv e = 0 from he]
    exact isHomogeneous_zero (Fin 4) ℤ d
  · exact he

end DualSepClusterLP.TrianglePacking

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

theorem ringValue_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : ℕ → R) (e : Expr) : f (ringValue x e) = ringValue (fun i => f (x i)) e := by
  induction e <;> simp [ringValue, *]

theorem ringValue_denote (ctx : Context ℝ) (e : Expr) :
    ringValue (fun i => ctx.get i) e = e.denote ctx := by
  induction e <;> simp [ringValue, Expr.denote, denoteInt_eq, Var.denote, *]

theorem ctx4_index4 (a b c d : ℝ) (i : ℕ) :
    (ctx4 a b c d).get i = (![a,b,c,d] : Fin 4 → ℝ) (index4 i) := by
  rcases i with _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  rw [Lean.RArray.get_eq_getImpl]
  simp [ctx4, Lean.RArray.getImpl, index4]

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

theorem eval_toMv {R : Type*} [CommRing R] (x : Fin 4 → R) (e : Expr) :
    (toMv e).eval₂ (Int.castRingHom R) x = ringValue (fun i => x (index4 i)) e := by
  induction e <;> simp [toMv, ringValue, index4, *]
  all_goals exact MvPolynomial.eval₂_C _ _ _

theorem packedOK_sound (e : Expr) (h : packedOK e = true) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ e.denote (ctx4 a b c d) := by
  simp only [packedOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg,hm⟩,hv⟩,hmask⟩ := h
  let w : Fin 4 → ℝ := ![a,b,c,d]
  have hx (i : Fin 4) : 0 ≤ w i := by fin_cases i <;> assumption
  have hh := packedPoly_sound (toMv e) (isHomogeneous_of_grade e 11 hg) 239
    (fun m _ => lt_of_le_of_lt (coeff_bound e m) (by exact_mod_cast hm))
    (packedValue e) ?_ hv hmask w hx
  · rw [eval_toMv] at hh
    rw [← ringValue_denote, show (fun i => (ctx4 a b c d).get i) =
        (fun i => w (index4 i)) from funext (ctx4_index4 a b c d)]
    exact hh
  · change packedValue e = (toMv e).eval₂ (RingHom.id ℤ) _
    have hid : RingHom.id ℤ = Int.castRingHom ℤ := by ext; rfl
    rw [hid, eval_toMv]
    unfold packedValue
    congr 1
    funext i
    rw [pow_mul]

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

theorem readForm_eval (q : Form) (u v w k : ℝ) :
    (readForm q).denote (ctx4 u v w k) = q.mix u v w k := by rfl

theorem totalForm_eval (s : Tet) (u v w k : ℝ) (m : u+v+w+k = 1) :
    (totalForm s).denote (ctx4 u v w k) = (s.den : ℝ) := by
  change (s.den : ℝ)*(u+v+w+k) = _; rw [m, mul_one]

theorem den_end (ep : ℕ) (x y z l : E) (ctx : Lean.RArray ℝ) :
    (endForm ep x y z l).denote ctx = endForm ep (x.denote ctx) (y.denote ctx)
      (z.denote ctx) (l.denote ctx) := by
  match ep with
  | 0 => exact de_zero _
  | 1 | 2 | 3 | 4 | 5 | _+6 => rfl

theorem end_scale (ep : ℕ) (x y z l : ℝ) :
    endForm ep (x*l) (y*l) (z*l) l = endpointValue ep x y z*l := by
  match ep with
  | 0 => change 0 = 0*l; ring
  | 1 => change x*l+y*l-l=(x+y-1)*l; ring
  | 2 => change x*l+z*l-l=(x+z-1)*l; ring
  | 3 => change y*l+z*l-l=(y+z-1)*l; ring
  | 4 | 5 | _+6 => rfl

theorem onTile (a b c ep : ℕ) (s : Tet) (ha : a ≤ 4) (hb : b ≤ 4) (hc : c ≤ 4) (hs : 0 < s.den)
    (good : ∀ u v w k : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → 0 ≤ k →
      0 ≤ (tileExpr a b c ep s).denote (ctx4 u v w k)) :
    OnTet (certificateProperty a b c ep) s := by
  intro u v w k hu hv hw hk mass
  let l : ℝ := s.den
  let x := s.X.mix u v w k/l
  let y := s.Y.mix u v w k/l
  let z := s.Z.mix u v w k/l
  change OnPiece a x → OnPiece b y → OnPiece c z → _
  intro hx hy hz
  have hl : 0 < l := by dsimp [l]; exact_mod_cast hs
  have ex : s.X.mix u v w k = x*l := (div_mul_cancel₀ _ hl.ne').symm
  have ey : s.Y.mix u v w k = y*l := (div_mul_cancel₀ _ hl.ne').symm
  have ez : s.Z.mix u v w k = z*l := (div_mul_cancel₀ _ hl.ne').symm
  have h := good u v w k hu hv hw hk
  dsimp only [tileExpr] at h
  rw [denote_homTriangle,den_end] at h
  simp only [readForm_eval, totalForm_eval s u v w k mass] at h
  change 0 ≤ homTriangle a b c _ _ _ (endForm ep _ _ _ l) l at h
  rw [ex,ey,ez,end_scale,triangle_scale _ _ _ _ _ _ _ _ ha hb hc hx hy hz] at h
  have X : 0 < 2-x := by linarith [onPiece_le_one _ _ hx]
  have Y : 0 < 2-y := by linarith [onPiece_le_one _ _ hy]
  have Z : 0 < 2-z := by linarith [onPiece_le_one _ _ hz]
  exact nonneg_of_mul_nonneg_right h (by positivity)

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

theorem validTiles_sound {a b c ep : ℕ} {tiles : Array Tile}
    (ha : a ≤ 4) (hb : b ≤ 4) (hc : c ≤ 4)
    (h : validTiles a b c ep tiles = true) (i : Fin tiles.size) :
    OnTet (certificateProperty a b c ep) tiles[i].1 := by
  obtain ⟨hp, he⟩ := Bool.and_eq_true_iff.mp (Array.all_eq_true.mp h i i.isLt)
  exact onTile _ _ _ _ _ ha hb hc (of_decide_eq_true hp) fun _ _ _ _ hu hv hw hk =>
    packedOK_sound _ he hu hv hw hk

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert
open TriGeo

theorem bernsteinBoxCertificateSound (a b c : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hc : c ≤ 4)
    (regions : Fin 8 → RegionCertificate) (h : acceptsBox a b c regions = true)
    (x y z : ℝ) (hx : OnPiece a x) (hy : OnPiece b y) (hz : OnPiece c z) : Ends a b c x y z := by
  intro feasible
  have allok : ∀ e : Fin 8, regionOK a b c e (regions e) = true := of_decide_eq_true h
  have regOK (e : Fin 8) (hreg : InRegion e x y z) :
      0 ≤ signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z (endpointValue (e.val-1) x y z) := by
    obtain ⟨cover, vals⟩ := Bool.and_eq_true_iff.mp (allok e)
    have hs := allForms_sat a b c e ha hb hc (by omega) x y z hx hy hz hreg
    exact Cover.sound (validTiles_sound ha hb hc vals) (regions e).cover (AllForms a b c e)
      cover x y z hs hx hy hz
  apply region_endpoints (fun t => 0 ≤ signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z t)
    x y z (onPiece_zero _ _ hx) (onPiece_zero _ _ hy) (onPiece_zero _ _ hz) feasible
  · exact regOK 0
  · exact regOK 1
  · exact regOK 2
  · exact regOK 3
  · exact regOK 4
  · exact regOK 5
  · exact regOK 6
  · exact regOK 7

end DualSepClusterLP.TriCert
namespace DualSepClusterLP.TriCert

private theorem turn (a b c : ℕ) (x y z : ℝ) : Ends a b c x y z ↔ Ends b c a y z x := by
  simp only [Ends, tripleLower, tripleUpper, signedTriangleSurplus,
    add_assoc, add_left_comm, add_comm, max_assoc, max_left_comm, max_comm,
    min_assoc, min_left_comm, min_comm]

private theorem incidentSwap (s q r : Bool) (x y z h : ℝ) :
    triangleSurplus s q r x y z h = triangleSurplus q s r y x z h := by
  simp only [triangleSurplus,oppositeSlack,mul_assoc,mul_left_comm,mul_comm,add_comm]

private theorem flip (a b c : ℕ) (x y z : ℝ) : Ends a b c x y z ↔ Ends b a c y x z := by
  simp only [Ends, tripleLower, tripleUpper, signedTriangleSurplus,
    incidentSwap (isPos a) (isPos c), incidentSwap (isPos b) (isPos a),
    incidentSwap (isPos c) (isPos b), add_assoc, add_left_comm, add_comm,
    max_assoc, max_left_comm, max_comm, min_assoc, min_left_comm, min_comm]


end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert
open TriGeo
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
theorem cell003Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 0 y) (hz : OnPiece 3 z) : Ends 0 0 3 x y z :=
  bernsteinBoxCertificateSound 0 0 3 (by decide) (by decide) (by decide) certifiedBox003.regions certifiedBox003.accepted x y z hx hy hz
theorem cell004Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 0 y) (hz : OnPiece 4 z) : Ends 0 0 4 x y z :=
  bernsteinBoxCertificateSound 0 0 4 (by decide) (by decide) (by decide) certifiedBox004.regions certifiedBox004.accepted x y z hx hy hz

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert
open TriGeo
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
theorem cell013Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 1 y) (hz : OnPiece 3 z) : Ends 0 1 3 x y z :=
  bernsteinBoxCertificateSound 0 1 3 (by decide) (by decide) (by decide) certifiedBox013.regions certifiedBox013.accepted x y z hx hy hz
theorem cell014Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 1 y) (hz : OnPiece 4 z) : Ends 0 1 4 x y z :=
  bernsteinBoxCertificateSound 0 1 4 (by decide) (by decide) (by decide) certifiedBox014.regions certifiedBox014.accepted x y z hx hy hz
theorem cell113Proof (x y z : ℝ) (hx : OnPiece 1 x) (hy : OnPiece 1 y) (hz : OnPiece 3 z) : Ends 1 1 3 x y z :=
  bernsteinBoxCertificateSound 1 1 3 (by decide) (by decide) (by decide) certifiedBox113.regions certifiedBox113.accepted x y z hx hy hz
theorem cell114Proof (x y z : ℝ) (hx : OnPiece 1 x) (hy : OnPiece 1 y) (hz : OnPiece 4 z) : Ends 1 1 4 x y z :=
  bernsteinBoxCertificateSound 1 1 4 (by decide) (by decide) (by decide) certifiedBox114.regions certifiedBox114.accepted x y z hx hy hz

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert
open TriGeo
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
theorem cell023Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 2 y) (hz : OnPiece 3 z) : Ends 0 2 3 x y z :=
  bernsteinBoxCertificateSound 0 2 3 (by decide) (by decide) (by decide) certifiedBox023.regions certifiedBox023.accepted x y z hx hy hz
theorem cell024Proof (x y z : ℝ) (hx : OnPiece 0 x) (hy : OnPiece 2 y) (hz : OnPiece 4 z) : Ends 0 2 4 x y z :=
  bernsteinBoxCertificateSound 0 2 4 (by decide) (by decide) (by decide) certifiedBox024.regions certifiedBox024.accepted x y z hx hy hz
theorem cell123Proof (x y z : ℝ) (hx : OnPiece 1 x) (hy : OnPiece 2 y) (hz : OnPiece 3 z) : Ends 1 2 3 x y z :=
  bernsteinBoxCertificateSound 1 2 3 (by decide) (by decide) (by decide) certifiedBox123.regions certifiedBox123.accepted x y z hx hy hz
theorem cell124Proof (x y z : ℝ) (hx : OnPiece 1 x) (hy : OnPiece 2 y) (hz : OnPiece 4 z) : Ends 1 2 4 x y z :=
  bernsteinBoxCertificateSound 1 2 4 (by decide) (by decide) (by decide) certifiedBox124.regions certifiedBox124.accepted x y z hx hy hz
theorem cell223Proof (x y z : ℝ) (hx : OnPiece 2 x) (hy : OnPiece 2 y) (hz : OnPiece 3 z) : Ends 2 2 3 x y z :=
  bernsteinBoxCertificateSound 2 2 3 (by decide) (by decide) (by decide) certifiedBox223.regions certifiedBox223.accepted x y z hx hy hz
theorem cell224Proof (x y z : ℝ) (hx : OnPiece 2 x) (hy : OnPiece 2 y) (hz : OnPiece 4 z) : Ends 2 2 4 x y z :=
  bernsteinBoxCertificateSound 2 2 4 (by decide) (by decide) (by decide) certifiedBox224.regions certifiedBox224.accepted x y z hx hy hz

end DualSepClusterLP.TriCert
namespace DualSepClusterLP.TriCert

theorem signCases
    (cell003Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 0 y → OnPiece 3 z → Ends 0 0 3 x y z)
    (cell004Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 0 y → OnPiece 4 z → Ends 0 0 4 x y z)
    (cell013Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 1 y → OnPiece 3 z → Ends 0 1 3 x y z)
    (cell014Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 1 y → OnPiece 4 z → Ends 0 1 4 x y z)
    (cell023Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 2 y → OnPiece 3 z → Ends 0 2 3 x y z)
    (cell024Proof : ∀ x y z : ℝ, OnPiece 0 x → OnPiece 2 y → OnPiece 4 z → Ends 0 2 4 x y z)
    (cell113Proof : ∀ x y z : ℝ, OnPiece 1 x → OnPiece 1 y → OnPiece 3 z → Ends 1 1 3 x y z)
    (cell114Proof : ∀ x y z : ℝ, OnPiece 1 x → OnPiece 1 y → OnPiece 4 z → Ends 1 1 4 x y z)
    (cell123Proof : ∀ x y z : ℝ, OnPiece 1 x → OnPiece 2 y → OnPiece 3 z → Ends 1 2 3 x y z)
    (cell124Proof : ∀ x y z : ℝ, OnPiece 1 x → OnPiece 2 y → OnPiece 4 z → Ends 1 2 4 x y z)
    (cell223Proof : ∀ x y z : ℝ, OnPiece 2 x → OnPiece 2 y → OnPiece 3 z → Ends 2 2 3 x y z)
    (cell224Proof : ∀ x y z : ℝ, OnPiece 2 x → OnPiece 2 y → OnPiece 4 z → Ends 2 2 4 x y z)
    (x y z : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (hn : tripleLower x y z ≤ tripleUpper x y z) :
    0 ≤ signedTriangleSurplus true true false x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus true true false x y z (tripleUpper x y z) := by
  have check : ∀ a b c : ℕ, a ≤ b → b < 3 → 3 ≤ c → c ≤ 4 → ∀ x y z : ℝ, OnPiece a x → OnPiece b y → OnPiece c z → Ends a b c x y z := by
    intro a b c hab hb hc hc4
    have ha : a ≤ 2 := by omega
    have hb2 : b ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first
      | omega
      | exact cell003Proof
      | exact cell004Proof
      | exact cell013Proof
      | exact cell014Proof
      | exact cell023Proof
      | exact cell024Proof
      | exact cell113Proof
      | exact cell114Proof
      | exact cell123Proof
      | exact cell124Proof
      | exact cell223Proof
      | exact cell224Proof
  obtain ⟨ha,ha4,hx'⟩ := choose_spec true hx
  have hapos : choose true x < 3 := of_decide_eq_true ha
  obtain ⟨hb,hb4,hy'⟩ := choose_spec true hy
  have hbpos : choose true y < 3 := of_decide_eq_true hb
  obtain ⟨hc,hc4,hz'⟩ := choose_spec false hz
  have hcneg : 3 ≤ choose false z := by simpa [isPos] using hc
  suffices h : Ends (choose true x) (choose true y) (choose false z) x y z by simpa only [ha,hb,hc] using h hn
  rcases le_total (choose true x) (choose true y) with hab|hba
  · exact check _ _ _ hab hbpos hcneg hc4 _ _ _ hx' hy' hz'
  · apply (flip ..).mpr
    exact check _ _ _ hba hapos hcneg hc4 _ _ _ hy' hx' hz'

end DualSepClusterLP.TriCert

open DualSepClusterLP DualSepClusterLP.TriCert

theorem solution (x y z : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (hn : tripleLower x y z ≤ tripleUpper x y z) :
    0 ≤ signedTriangleSurplus true true false x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus true true false x y z (tripleUpper x y z) :=
  signCases
    cell003Proof cell004Proof cell013Proof cell014Proof cell023Proof cell024Proof cell113Proof cell114Proof cell123Proof cell124Proof cell223Proof cell224Proof
    x y z hx hy hz hn

