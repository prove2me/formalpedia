-- Prove2me | solution 1 for DetDLP.ecdlp_short_weierstrass_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T20:53:23.344809+00:00
-- url     : https://prove2.me/submissions/d54e2d23-80c9-4841-8bcf-ee165b7d6316

import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_ToTuring_Lib_Nat1b
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Definitions.Def_DetDLP_M89_MachineComp
import Definitions.Def_DetDLP_PolyTBridge

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace DetDLP.w2_algebra
open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve F)

def short : WeierstrassCurve F := ⟨0, 0, 0, -27 * E.c₄, -54 * E.c₆⟩
def X (x : F) := 36 * x + 3 * E.b₂
def Y (x y : F) := 108 * (2 * y + E.a₁ * x + E.a₃)

theorem disc : (short E).Δ = 6 ^ 12 * E.Δ := by
  simp only [short, Δ, b₈, c₄, c₆, b₂, b₄, b₆]
  ring

theorem elliptic [E.IsElliptic] (h6 : (6 : F) ≠ 0) : (short E).IsElliptic :=
  ⟨by rw [disc]; exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 12 h6)).mul E.isUnit_Δ⟩

theorem equation (h6 : (6 : F) ≠ 0) (x y : F) :
    (short E).toAffine.Equation (X E x) (Y E x y) ↔ E.toAffine.Equation x y := by
  rw [equation_iff', equation_iff']
  have h := pow_ne_zero 6 h6
  convert (mul_eq_zero.trans (or_iff_right h) : (6:F)^6 * _ = 0 ↔ _) using 2
  simp only [short, X, Y, c₄, c₆, b₂, b₄, b₆, WeierstrassCurve.toAffine]
  ring

variable [E.IsElliptic]

def point (h6 : (6:F) ≠ 0) : E.toAffine.Point → (short E).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (X E x) (Y E x y) (by
      letI := elliptic E h6
      exact equation_iff_nonsingular.mp ((equation E h6 x y).2 h.1))

variable (h6 : (6:F) ≠ 0)

include h6 in
private theorem nz36 : (36:F) ≠ 0 := by
  convert pow_ne_zero 2 h6 using 1 <;> norm_num
include h6 in
private theorem nz216 : (216:F) ≠ 0 := by
  convert pow_ne_zero 3 h6 using 1 <;> norm_num

include h6 in
private theorem X_inj (x z : F) : X E x = X E z ↔ x = z := by
  simp only [X, add_left_inj, mul_right_inj' (nz36 h6)]

include h6 in
private theorem Y_inj (x y w : F) : Y E x y = Y E x w ↔ y = w := by
  have H (v : F) : Y E x v = 216 * v + 108*(E.a₁*x+E.a₃) := by unfold Y; ring
  simp only [H, add_left_inj, mul_right_inj' (nz216 h6)]

private theorem Y_neg (x y : F) :
    Y E x (E.toAffine.negY x y) = (short E).toAffine.negY (X E x) (Y E x y) := by
  simp only [Y, negY, short, WeierstrassCurve.toAffine]; ring

private theorem point_bij : Function.Bijective (point E h6) := by
  constructor
  · intro P Q h
    cases P <;> cases Q <;> simp only [point, Point.some.injEq, reduceCtorEq] at h ⊢
    · obtain ⟨hx, hy⟩ := h
      obtain rfl := (X_inj E h6 ..).1 hx
      exact ⟨rfl, (Y_inj E h6 ..).1 hy⟩
  · rintro (_ | ⟨v, w, hw⟩)
    · exact ⟨.zero, rfl⟩
    · let x := (v - 3 * E.b₂) / 36
      let y := (w - 108 * (E.a₁*x+E.a₃)) / 216
      have hx : X E x = v := by unfold X x; field_simp [nz36 h6]; ring
      have hy : Y E x y = w := by unfold Y y; field_simp [nz216 h6]; ring
      have hn : E.toAffine.Nonsingular x y := equation_iff_nonsingular.mp <|
        (equation E h6 x y).mp (hx ▸ hy ▸ hw.1)
      exact ⟨.some x y hn, by simp only [point, Point.some.injEq, hx, hy, and_self]⟩

variable [DecidableEq F]

include h6 in
private theorem slope_transport {x z y w : F} (hp : E.toAffine.Nonsingular x y)
    (hq : E.toAffine.Nonsingular z w) (hn : ¬(x = z ∧ y = E.toAffine.negY z w)) :
    (short E).toAffine.slope (X E x) (X E z) (Y E x y) (Y E z w) =
      6 * E.toAffine.slope x z y w + 3 * E.a₁ := by
  by_cases hx : x = z
  · subst z
    have hn' : y ≠ E.toAffine.negY x w := fun h => hn ⟨rfl,h⟩
    obtain rfl := Y_eq_of_Y_ne hp.1 hq.1 rfl hn'
    have h' : Y E x y ≠ (short E).toAffine.negY (X E x) (Y E x y) := by
      rw [← Y_neg]; exact fun h => hn' ((Y_inj E h6 ..).1 h)
    rw [slope_of_Y_ne rfl h', slope_of_Y_ne rfl hn']
    have ho := sub_ne_zero.mpr hn'
    have ht := sub_ne_zero.mpr h'
    field_simp [ho, ht]
    simp only [short, X, Y, negY, c₄, b₂, b₄, WeierstrassCurve.toAffine]; ring
  · have hx' := fun h => hx ((X_inj E h6 ..).1 h)
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx', sub_ne_zero.mpr hx]
    simp only [X, Y]; ring

private theorem addX_transport (x z m : F) :
    X E (E.toAffine.addX x z m) = (short E).toAffine.addX (X E x) (X E z) (6*m+3*E.a₁) := by
  simp only [X, addX, short, b₂, WeierstrassCurve.toAffine]; ring

private theorem addY_transport (x z y m : F) :
    Y E (E.toAffine.addX x z m) (E.toAffine.addY x z y m) =
      (short E).toAffine.addY (X E x) (X E z) (Y E x y) (6*m+3*E.a₁) := by
  simp only [X, Y, addX, addY, negAddY, negY, short, b₂, WeierstrassCurve.toAffine]; ring

theorem additive (P Q : E.toAffine.Point) : point E h6 (P+Q) = point E h6 P + point E h6 Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some z w hq =>
      have H : (X E x = X E z ∧ Y E x y = (short E).toAffine.negY (X E z) (Y E z w)) ↔
          (x = z ∧ y = E.toAffine.negY z w) := by
        rw [X_inj E h6]; refine and_congr_right fun hx => ?_
        subst z; rw [← Y_neg, Y_inj E h6]
      by_cases hn : x = z ∧ y = E.toAffine.negY z w
      · obtain ⟨ha,hb⟩ := H.2 hn
        rw [Point.add_of_Y_eq hn.1 hn.2]; simp only [point, Point.add_of_Y_eq ha hb]; rfl
      · rw [Point.add_some hn]; simp only [point, Point.add_some (mt H.1 hn), Point.some.injEq,
          slope_transport E h6 hp hq hn]
        exact ⟨addX_transport E .., addY_transport E ..⟩

noncomputable def equiv : E.toAffine.Point ≃+ (short E).toAffine.Point :=
  AddEquiv.ofBijective (⟨⟨point E h6, rfl⟩, additive E h6⟩ : E.toAffine.Point →+ (short E).toAffine.Point)
    (point_bij E h6)

end DetDLP.w2_algebra

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.w2_codec
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open WeierstrassCurve Groundwork Groundwork.PolyT

/- A scan consumes one framed field; its counter is the input list itself. -/
abbrev State := Bool × List Bool × List Bool

def scan (s : State) (_ : Bool) : State :=
  bif s.1 then s else bif s.2.1.headD false then
    (false, s.2.1.tail.tail, s.2.1.tail.headD false :: s.2.2)
  else (true, s.2.1.tail, s.2.2)

def splitField (w : List Bool) : List Bool × List Bool :=
  let s := w.foldl scan (false, w.tail, [])
  (s.2.2.reverse, s.2.1)

private theorem scan_done (clock tail acc : List Bool) :
    clock.foldl scan (true, tail, acc) = (true, tail, acc) := by
  induction clock <;> simp_all [scan]

private theorem scan_spec (clock u tail acc : List Bool) (h : u.length < clock.length) :
    clock.foldl scan (false, Encoding.frame u ++ tail, acc) =
      (true, tail, u.reverse ++ acc) := by
  induction u generalizing clock acc with
  | nil => cases clock <;> simp_all [Encoding.frame, scan, scan_done]
  | cons b u ih =>
    cases clock with
    | nil => simp at h
    | cons e clock =>
      simp only [List.length_cons] at h
      simpa only [List.foldl_cons, Encoding.frame, List.foldr_cons, List.cons_append,
        scan, List.headD_cons, List.tail_cons, Bool.false_eq_true, cond_false, cond_true,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using
          ih clock (b::acc) (by omega)

private theorem frame_len (u : List Bool) : (Encoding.frame u).length = 2*u.length+1 := by
  induction u with
  | nil => rfl
  | cons b u ih => change (Encoding.frame u).length+1+1 = _; rw [ih]; simp; omega

@[simp] theorem split_spec (u t : List Bool) :
    splitField (true :: (Encoding.frame u ++ t)) = (u,t) := by
  unfold splitField
  simp only [List.tail_cons]
  rw [scan_spec _ _ _ _ (by simp [frame_len]; omega)]
  simp

def field : ℕ → List Bool → ℕ
  | 0, w => bval (splitField w).1
  | i+1, w => field i (splitField w).2

@[simp] theorem bval_count (n : ℕ) : bval (countWord n) = n := by
  by_cases h : n = 0
  · subst n; rfl
  · simp [countWord, h, bval_bits]

@[simp] theorem field_cons0 (n : ℕ) (l : List ℕ) :
    field 0 (encodeNatListBin (n::l)) = n := by
  simp [field, encodeNatListBin, Encoding.encodeList]
@[simp] theorem field_consS (i n : ℕ) (l : List ℕ) :
    field (i+1) (encodeNatListBin (n::l)) = field i (encodeNatListBin l) := by
  simp [field, encodeNatListBin, Encoding.encodeList]

def negN (p n : ℕ) := p - n % p
def b2 (a b : ℕ) := a*a+4*b
def b4 (a c d : ℕ) := 2*d+a*c
def b6 (c e : ℕ) := c*c+4*e
def a4 (p a b c d : ℕ) :=
  (27 * (24*b4 a c d + negN p (b2 a b * b2 a b))) % p
def a6 (p a b c d e : ℕ) :=
  (54 * (b2 a b * b2 a b * b2 a b + negN p (36*b2 a b*b4 a c d) + 216*b6 c e)) % p

def pt (p a b c tag x y : ℕ) : List ℕ :=
  if tag = 0 then [0, (36*x+3*b2 a b)%p, (108*(2*y+a*x+c))%p] else [1,0,0]

def transform (p a b c d e u x y v z w : ℕ) :=
  [p,0,0,0,a4 p a b c d,a6 p a b c d e] ++ pt p a b c u x y ++ pt p a b c v z w

def pre (input : List Bool) : List Bool :=
  encodeNatListBin (transform (field 0 input) (field 1 input) (field 2 input) (field 3 input)
    (field 4 input) (field 5 input) (field 6 input) (field 7 input) (field 8 input)
    (field 9 input) (field 10 input) (field 11 input))

private theorem castNeg (p n : ℕ) [NeZero p] : (negN p n : ZMod p) = -(n : ZMod p) := by
  rw [negN, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (NeZero.pos p))), ZMod.natCast_self,
    zero_sub, ZMod.natCast_mod]

private theorem coeff4 {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    a4 p E.a₁.val E.a₂.val E.a₃.val E.a₄.val = (w2_algebra.short E).a₄.val := by
  unfold a4
  rw [← ZMod.val_natCast]
  congr 1
  push_cast [ZMod.natCast_zmod_val, castNeg, b2, b4, w2_algebra.short, c₄, b₂, b₄]
  ring

private theorem coeff6 {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    a6 p E.a₁.val E.a₂.val E.a₃.val E.a₄.val E.a₆.val = (w2_algebra.short E).a₆.val := by
  unfold a6
  rw [← ZMod.val_natCast]
  congr 1
  push_cast [ZMod.natCast_zmod_val, castNeg, b2, b4, b6, w2_algebra.short, c₆, b₂, b₄, b₆]
  ring

private theorem coordX {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (x : ZMod p) :
    (36*x.val+3*b2 E.a₁.val E.a₂.val)%p = (w2_algebra.X E x).val := by
  rw [← ZMod.val_natCast]; congr 1; push_cast [ZMod.natCast_zmod_val, b2, w2_algebra.X, b₂]; ring
private theorem coordY {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (x y : ZMod p) :
    (108*(2*y.val+E.a₁.val*x.val+E.a₃.val))%p = (w2_algebra.Y E x y).val := by
  rw [← ZMod.val_natCast]; congr 1; push_cast [ZMod.natCast_zmod_val, w2_algebra.Y]; ring

theorem encoded {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (h6 : (6 : ZMod p) ≠ 0) (P Q : E.toAffine.Point) :
    pre (encodeECDLPInput p E P Q) = encodeECDLPInput p (w2_algebra.short E)
      (w2_algebra.equiv E h6 P) (w2_algebra.equiv E h6 Q) := by
  change _ = encodeECDLPInput p _ (w2_algebra.point E h6 P) (w2_algebra.point E h6 Q)
  cases P <;> cases Q <;>
    simp only [pre, encodeECDLPInput, pointCoords, w2_algebra.point, List.cons_append,
      List.nil_append, show (0 : ZMod p).val = 0 from ZMod.val_zero,
      show (w2_algebra.short E).a₁.val = 0 from ZMod.val_zero,
      show (w2_algebra.short E).a₂.val = 0 from ZMod.val_zero,
      show (w2_algebra.short E).a₃.val = 0 from ZMod.val_zero,
      Nat.reduceAdd, field_cons0, field_consS, transform, pt,
      coeff4, coeff6, coordX, coordY, ↓reduceIte, reduceCtorEq]

end DetDLP.w2_codec

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DetDLP.w2_codec
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork Groundwork.PolyT
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst
  Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.flatMap Groundwork.PolyT.mod
  Groundwork.PolyT.mul P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

variable {α : Type} [Enc α]

private theorem scan_size (s : State) (b : Bool) : len (scan s b) ≤ len s+3 := by
  rcases s with ⟨flag,w,acc⟩
  cases flag <;> unfold scan <;> simp only [cond_true, cond_false]
  · cases h : w.headD false <;> simp [len_pair, len_bool, len_bools] <;> omega
  · omega

@[local fun_prop] theorem split_poly {f : α → List Bool} (h : PolyT f) :
    PolyT (fun x => splitField (f x)) := by
  have hs : PolyT fun x => (f x).foldl scan (false, (f x).tail, []) := by
    refine foldl_add (g := fun _ => scan) h (by fun_prop) (by unfold scan; fun_prop) ?_
    exact ⟨fun _ => 3, PB.const 3, fun _ s e _ => scan_size s e⟩
  unfold splitField; fun_prop

@[local fun_prop] theorem field_poly (i : ℕ) {f : α → List Bool} (h : PolyT f) :
    PolyT (fun x => field i (f x)) := by
  induction i generalizing f with
  | zero => simp only [field]; fun_prop
  | succ i ih => simp only [field]; apply ih; fun_prop

@[local fun_prop] theorem cw_poly {f : α → ℕ} (h : PolyT f) :
    PolyT (fun x => countWord (f x)) := by unfold countWord; fun_prop

private theorem frame_flat (w : List Bool) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame, List.flatMap] using congrArg (fun u => true::b::u) ih

private theorem encode_flat (ns : List ℕ) : encodeNatListBin ns =
    ns.flatMap (fun n => true :: Encoding.frame (countWord n)) ++ [false] := by
  induction ns with
  | nil => rfl
  | cons n ns ih => change true :: (Encoding.frame (countWord n) ++ encodeNatListBin ns) = _
                    rw [ih]; simp [List.flatMap, List.append_assoc]

@[local fun_prop] theorem encode_poly {f : α → List ℕ} (h : PolyT f) :
    PolyT (fun x => encodeNatListBin (f x)) := by
  simp only [encode_flat, frame_flat]; fun_prop

@[local fun_prop] private theorem neg_poly {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => negN (f x) (g x)) := by unfold negN; fun_prop
@[local fun_prop] private theorem b2_poly {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => b2 (f x) (g x)) := by unfold b2; fun_prop
@[local fun_prop] private theorem b4_poly {f g h : α → ℕ} (hf : PolyT f) (hg : PolyT g) (hh : PolyT h) :
    PolyT (fun x => b4 (f x) (g x) (h x)) := by unfold b4; fun_prop
@[local fun_prop] private theorem b6_poly {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => b6 (f x) (g x)) := by unfold b6; fun_prop
@[local fun_prop] private theorem a4_poly {p a b c d : α → ℕ} (hp : PolyT p) (ha : PolyT a)
    (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) : PolyT (fun x => a4 (p x) (a x) (b x) (c x) (d x)) := by
  unfold a4; fun_prop
@[local fun_prop] private theorem a6_poly {p a b c d e : α → ℕ} (hp : PolyT p) (ha : PolyT a)
    (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) (he : PolyT e) :
    PolyT (fun x => a6 (p x) (a x) (b x) (c x) (d x) (e x)) := by unfold a6; fun_prop
@[local fun_prop] private theorem pt_poly {p a b c t i j : α → ℕ} (hp : PolyT p) (ha : PolyT a)
    (hb : PolyT b) (hc : PolyT c) (ht : PolyT t) (hi : PolyT i) (hj : PolyT j) :
    PolyT (fun x => pt (p x) (a x) (b x) (c x) (t x) (i x) (j x)) := by unfold pt; fun_prop

theorem pre_poly : PolyT pre := by unfold pre transform; fun_prop
end DetDLP.w2_codec

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace DetDLP.w2_pipeline
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
  OAI.Algorithms.SubexponentialSAT.SqrtLogSpace MachineComposition

structure Wire (B : PrimitiveMachine) (N : ℕ) where
  tape : Fin B.tapeCount → Fin N
  src : Fin N → Fin B.tapeCount
  back : Function.LeftInverse src tape

def body {B N} (W : Wire B N) : Program N :=
  ⟨B.stateCount, B.start, W.tape ∘ B.scan, B.transition⟩

structure Box (n : ℕ) where
  pos : Fin n → ℤ
  lo : Fin n → ℤ
  hi : Fin n → ℤ

def box {A : PrimitiveMachine} (c : LocatedCfg A) : Box A.tapeCount :=
  ⟨c.position, c.lower, c.upper⟩

def Box.move {n} (b : Box n) (i : Fin n) (k : ℤ) : Box n :=
  ⟨Function.update b.pos i (b.pos i + k), Function.update b.lo i (min (b.lo i) (b.pos i+k)),
    Function.update b.hi i (max (b.hi i) (b.pos i+k))⟩

structure Covers {B N} (W : Wire B N) (seed d : Box N) (c : Box B.tapeCount) : Prop where
  pos : ∀ i, d.pos (W.tape i) = seed.pos (W.tape i) + c.pos i
  lo : ∀ j, seed.lo j + c.lo (W.src j) ≤ d.lo j
  hi : ∀ j, d.hi j ≤ seed.hi j + c.hi (W.src j)

def Valid {n} (s : Box n) := ∀ j, s.lo j ≤ s.pos j ∧ s.pos j ≤ s.hi j

private theorem move_covers {B N} {W : Wire B N} {s d c} (hv : Valid s) (h : Covers W s d c)
    (i : Fin B.tapeCount) (k : ℤ) : Covers W s (d.move (W.tape i) k) (c.move i k) := by
  constructor
  · intro j; by_cases hj : j = i
    · subst j; simp [Box.move, h.pos, add_assoc]
    · simp [Box.move, hj, W.back.injective.ne hj, h.pos]
  · intro j; by_cases hj : j = W.tape i
    · subst j
      simp only [Box.move, Function.update_self, W.back i, h.pos]
      have hu := h.lo (W.tape i); rw [W.back] at hu
      have := (hv (W.tape i)).1
      omega
    · have hu := h.lo j
      simp only [Box.move, Function.update_of_ne hj]
      by_cases hj' : W.src j = i
      · simp only [hj', Function.update_self] at *; omega
      · simpa [hj'] using hu
  · intro j; by_cases hj : j = W.tape i
    · subst j
      simp only [Box.move, Function.update_self, W.back i, h.pos]
      have hu := h.hi (W.tape i); rw [W.back] at hu
      have := (hv (W.tape i)).2
      omega
    · have hu := h.hi j
      simp only [Box.move, Function.update_of_ne hj]
      by_cases hj' : W.src j = i
      · simp only [hj', Function.update_self] at *; omega
      · simpa [hj'] using hu

variable {B : PrimitiveMachine} {N : ℕ} (W : Wire B N) (inp : Fin N)
abbrev live := (body W).machine inp

structure Regs (c : B.Cfg) (d : (live W inp).Cfg) : Prop where
  state : d.state = c.state
  tapes : ∀ i, d.tapes (W.tape i) = c.tapes i

private theorem sim_cfg {c c' : B.Cfg} {d : (live W inp).Cfg} (h : Regs W inp c d)
    (hs : B.step c = some c') : ∃ d', (live W inp).step d = some d' ∧ Regs W inp c' d' := by
  rcases c with ⟨q,ts⟩; rcases d with ⟨q',ds⟩
  obtain ⟨hsq,ht⟩ := h
  change q' = q at hsq
  subst q'
  cases q with
  | inl b => simp [PrimitiveMachine.step] at hs
  | inr q =>
    simp only [PrimitiveMachine.step, live, body, Program.machine, Function.comp_apply] at hs ⊢
    change ∀ i, ds (W.tape i) = ts i at ht
    rw [ht]
    cases ht' : B.transition q (ts (B.scan q)).head with
    | inl b =>
      simp [ht'] at hs; subst c'
      exact ⟨_, rfl, rfl, ht⟩
    | inr qa =>
      rcases qa with ⟨q',a⟩
      simp only [ht', Option.some.injEq] at hs; subst c'
      refine ⟨_,rfl,rfl,?_⟩
      intro j
      by_cases hj : j = B.scan q
      · subst j; simp [Function.update_apply, ht, live, body, Program.machine] 
      · simp [Function.update_apply, hj, W.back.injective.ne hj, ht, live, body, Program.machine]

private theorem sim_monitor (s : Box N) (hv : Valid s) {c : LocatedCfg B} {d : LocatedCfg (live W inp)}
    (h : Regs W inp c.config d.config) (hc : Covers W s (box d) (box c)) (c' : B.Cfg) (d' : (live W inp).Cfg) :
    Covers W s (box (d.monitor d')) (box (c.monitor c')) := by
  simp only [LocatedCfg.monitor, h.state]
  cases hq : c.config.state with
  | inl b => exact hc
  | inr q =>
    simp only [Sum.elim_inr, live, body, Program.machine, Function.comp_apply, h.tapes]
    cases ht : B.transition q (c.config.tapes (B.scan q)).head with
    | inl b => exact hc
    | inr qa => exact move_covers hv hc (B.scan q) (headDisplacement qa.2)

private theorem monitor_cfg {A : PrimitiveMachine} (a : LocatedCfg A) (b : A.Cfg) :
    (a.monitor b).config = b := by
  unfold LocatedCfg.monitor
  cases hq : a.config.state with
  | inl k => rfl
  | inr q =>
    simp only [Sum.elim_inr]
    cases ht : A.transition q (a.config.tapes (A.scan q)).head <;> rfl

private theorem sim_trace (s : Box N) (hv : Valid s) {c c' : LocatedCfg B} {n : ℕ}
    (tr : Computation.Trace (locatedStep B) n c c') {d : LocatedCfg (live W inp)}
    (h : Regs W inp c.config d.config) (hc : Covers W s (box d) (box c)) :
    ∃ d', Computation.Trace (locatedStep (live W inp)) n d d' ∧ Regs W inp c'.config d'.config ∧
      Covers W s (box d') (box c') := by
  induction tr generalizing d with
  | refl => exact ⟨_,.refl _,h,hc⟩
  | @cons n a b e hab tr ih =>
    unfold locatedStep at hab
    cases ha : B.step a.config with
    | none => simp [ha] at hab
    | some a' =>
      simp [ha] at hab; subst b
      obtain ⟨d',hd',hr⟩ := sim_cfg W inp h ha
      have hh : Regs W inp (a.monitor a').config (d.monitor d').config := by
        simpa only [monitor_cfg] using hr
      obtain ⟨f,hf,he,hb⟩ := ih hh (sim_monitor W inp s hv h hc a' d')
      exact ⟨f,.cons (by simp [locatedStep, hd']) hf,he,hb⟩

private theorem sim_space {S : PrimitiveMachine} (seed : LocatedCfg S) (c : LocatedCfg B)
    {W : Wire B S.tapeCount} (v : Box S.tapeCount) (cov : Covers W (box seed) v (box c)) :
      (∑ j, (v.hi j - v.lo j + 1).toNat) ≤ visitedSpace seed + S.tapeCount * visitedSpace c := by
    calc
      _ ≤ ∑ j, ((seed.upper j - seed.lower j + 1).toNat + visitedSpace c) := by
        apply Finset.sum_le_sum; intro j _
        have hl := cov.lo j; have hu := cov.hi j
        have hs : (c.upper (W.src j) - c.lower (W.src j) + 1).toNat ≤ visitedSpace c :=
          Finset.single_le_sum (f := fun i => (c.upper i - c.lower i + 1).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (W.src j))
        simp only [box] at hl hu; omega
      _ = _ := by simp [Finset.sum_add_distrib, visitedSpace]

section Pipeline
variable (A B : PrimitiveMachine) (out : Fin A.tapeCount)

private theorem right_ne {m n} (i : Fin n) (j : Fin m) : Fin.natAdd m i ≠ Fin.castAdd n j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/-- The second machine reuses the first output tape as its input; all its other tapes are fresh. -/
def wire : Wire B (A.tapeCount+B.tapeCount) where
  tape i := if i = B.inputTape then Fin.castAdd B.tapeCount out else Fin.natAdd A.tapeCount i
  src := Fin.addCases (fun _ => B.inputTape) id
  back i := by by_cases h : i = B.inputTape <;> simp [h]

abbrev pipeline := thenMachine (addTapes A B.tapeCount) (body (wire A B out))

variable {A B out}
theorem run {outB : Fin B.tapeCount} {u v w : List Bool} {t₁ s₁ t₂ s₂ : ℝ}
    (ha : RunsWithin A out u v t₁ s₁) (hb : RunsWithin B outB v w t₂ s₂) :
    RunsWithin (pipeline A B out) ((wire A B out).tape outB) u w (t₁+t₂)
      (s₁+B.tapeCount + (A.tapeCount+B.tapeCount : ℕ)*s₂) := by
  let A' := addTapes A B.tapeCount
  let W := wire A B out
  let D := body W
  obtain ⟨m,a,ha,haltA,outA,timeA⟩ := (runsWithin_iff_segment ..).1 ha
  obtain ⟨n,b,hb,haltB,outB',timeB⟩ := (runsWithin_iff_segment ..).1 hb
  let a' := addTapesLocated A B.tapeCount a
  have trA : Segment A' (locatedInit A' u) a' m (s₁+B.tapeCount) := by
    rw [segment_iff_final_space]
    constructor
    · rw [show locatedInit A' u = _ from addTapesLocated_init A B.tapeCount u]
      exact MachineComposition.Trace.map (addTapesLocated A B.tapeCount)
        (fun c c' hc => by simp [A', hc]) ha.1
    · simpa [a', A', Nat.cast_add] using add_le_add_right (segment_iff_final_space.mp ha).2 (B.tapeCount:ℝ)
  have seedOK : Valid (box a') := locatedWellFormed_reachable trA.1
  let entry := restartCfg A' D a'
  have reg : Regs W A'.inputTape (locatedInit B v).config entry.config := by
    refine ⟨rfl,?_⟩
    intro i
    by_cases hi : i = B.inputTape
    · subst i; simpa [entry, restartCfg, a', addTapesLocated, addTapesCfg, W, wire, locatedInit,
        PrimitiveMachine.init] using outA
    · simp [entry, restartCfg, a', addTapesLocated, addTapesCfg, W, wire, locatedInit, PrimitiveMachine.init, hi]
  have cv : Covers W (box a') (box entry) (box (locatedInit B v)) := by
    constructor
    · intro i; simp [entry,restartCfg,box,locatedInit]
    · intro j; simp [entry,restartCfg,box,locatedInit]
    · intro j; simp only [entry,restartCfg,box,locatedInit]
      split <;> apply le_add_of_nonneg_right <;> exact Int.ofNat_nonneg _
  obtain ⟨fin,tr,regs,cov⟩ := sim_trace W A'.inputTape (box a') seedOK hb.1 reg cv
  have spaceB : (visitedSpace fin : ℝ) ≤ s₁+B.tapeCount+(A.tapeCount+B.tapeCount:ℕ)*s₂ := by
    have hs : visitedSpace fin ≤ visitedSpace a' + A'.tapeCount * visitedSpace b :=
      sim_space a' b (box (A := live W A'.inputTape) fin) cov
    have hs' : (visitedSpace fin : ℝ) ≤ visitedSpace a' + (A'.tapeCount:ℝ)*visitedSpace b := by exact_mod_cast hs
    exact hs'.trans (add_le_add (segment_iff_final_space.mp trA).2
      (mul_le_mul_of_nonneg_left (segment_iff_final_space.mp hb).2 (Nat.cast_nonneg _)))
  have res := thenMachine_runsWithin_add A' D (W.tape outB) u w trA haltA
    (segment_iff_final_space.mpr ⟨tr,spaceB⟩) (haltB.imp (fun _ h => regs.state.trans h))
    ((regs.tapes outB).trans outB') timeA timeB
  apply runsWithin_mono res le_rfl
  apply max_le _ le_rfl
  have sb := (Nat.cast_nonneg (visitedSpace b)).trans (segment_iff_final_space.mp hb).2
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) sb)

end Pipeline
end DetDLP.w2_pipeline

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.w2_bounds
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem frameLen (w : List Bool) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1 = _; rw [ih]; simp; omega

private theorem word_le {b p x : ℕ} (h : p ≤ 2^b) (hx : x ≤ p) : (countWord x).length ≤ b+1 := by
  by_cases hz : x = 0
  · simp [countWord,hz]
  · simp only [countWord, if_neg hz, Nat.size_eq_bits_len, Nat.size_le]
    have : 0 < 2^b := Nat.two_pow_pos b
    rw [pow_succ]; omega

private theorem listLen (b p : ℕ) (hp : p ≤ 2^b) (l : List ℕ) (hl : ∀ n ∈ l, n ≤ p) :
    (encodeNatListBin l).length ≤ l.length*(2*(b+1)+2)+1 := by
  induction l with
  | nil => simp [encodeNatListBin, Encoding.encodeList]
  | cons n l ih =>
    change (true :: (Encoding.frame (countWord n) ++ encodeNatListBin l)).length ≤ _
    simp only [List.length_cons, List.length_append, frameLen, Nat.add_mul, Nat.one_mul]
    have hu := word_le hp (hl n (by simp))
    have hv := ih (fun i hi => hl i (by simp [hi])); omega

theorem inputLen {p : ℕ} [NeZero p] (E : WeierstrassCurve (ZMod p)) (P Q : E.toAffine.Point) :
    (encodeECDLPInput p E P Q).length ≤ 50*(bitLen p+1) := by
  let l := [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] ++ pointCoords P ++ pointCoords Q
  have hl : ∀ x ∈ l, x ≤ p := by
    cases P <;> cases Q <;> simp [l, pointCoords, ZMod.val_lt, Nat.le_of_lt, Nat.one_le_iff_ne_zero,
      NeZero.ne p, (fun x : ZMod p => (ZMod.val_lt x).le)]
  have len : l.length = 12 := by cases P <;> cases Q <;> rfl
  have h := listLen (bitLen p) p (Nat.le_pow_clog (by decide) _) l hl
  change (encodeNatListBin l).length ≤ _; rw [len] at h; omega

private theorem logb_le {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 2*x := by
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
  nlinarith [Real.log_two_gt_d9, mul_nonneg (by linarith : (0:ℝ) ≤ x)
    (show 0 ≤ Real.log 2 - 1/2 by linarith [Real.log_two_gt_d9])]

private theorem denoms {b : ℝ} (hb : 2 ≤ b) :
    (0 < Real.sqrt (logLogSafe b) ∧ Real.sqrt (logLogSafe b) ≤ 2*Real.sqrt b) ∧
    (0 < (logSafe b) ^ ((1:ℝ)/4) ∧ (logSafe b) ^ ((1:ℝ)/4) ≤ 2*Real.sqrt b) := by
  have h₂ := logb_le (by linarith : 1 ≤ b)
  have hs : 1 ≤ logSafe b := le_max_left ..
  have ht : 1 ≤ logLogSafe b := le_max_left ..
  have H : logSafe b ≤ 4*b := by unfold logSafe; rw [max_eq_right hb]; exact max_le (by linarith) (by linarith)
  have J : logLogSafe b ≤ 4*b := by
    unfold logLogSafe; rw [max_eq_right hb]
    have h : max 2 (Real.logb 2 b) ≤ 2*b := max_le (by linarith) h₂
    have h' := logb_le (le_max_left (2:ℝ) (Real.logb 2 b) |>.trans' (by norm_num : (1:ℝ) ≤ 2))
    exact max_le (by linarith) (by linarith)
  have hh (x : ℝ) (hx : 0 ≤ x) (h : x ≤ 4*b) : Real.sqrt x ≤ 2*Real.sqrt b := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt (by linarith : 0 ≤ b), Real.sqrt_nonneg x, Real.sqrt_nonneg b]
  refine ⟨⟨Real.sqrt_pos.2 (by linarith), hh _ (by linarith) J⟩,
    Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  calc
    _ ≤ (logSafe b) ^ ((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
    _ = _ := (Real.sqrt_eq_rpow _).symm
    _ ≤ _ := hh _ (by linarith) H

private theorem pow_control {b : ℝ} (hb : 1 ≤ b) : b ≤ (2:ℝ)^(4*Real.sqrt b) := by
  apply (Real.logb_le_iff_le_rpow (by norm_num) (by linarith)).mp
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_le_rpow_div (by linarith : 0 ≤ b) (by norm_num : 0 < (1:ℝ)/2)
  rw [← Real.sqrt_eq_rpow] at h
  nlinarith [mul_nonneg (Real.sqrt_nonneg b)
    (show 0 ≤ Real.log 2 - 1/2 by linarith [Real.log_two_gt_d9])]

private theorem absorb (K T : ℕ) : ∃ D : ℕ, ∀ b l C : ℕ, 2 ≤ b → l ≤ 50*(b+1) →
    ∀ d : ℝ, 0 < d → d ≤ 2*Real.sqrt b →
      polyBound K l + T + T * (2:ℝ)^((C:ℝ)*b/d) ≤ (2:ℝ)^(((C+D:ℕ):ℝ)*b/d) := by
  let a := K*102^K
  let c := a+T+T
  refine ⟨2*(c+4*K), ?_⟩
  intro b l C hb hl d hd hds
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hl' : (l:ℝ)+1 ≤ 102*b := by exact_mod_cast (show l+1 ≤ 102*b by omega)
  have hp : polyBound K l ≤ (a:ℝ)*(b:ℝ)^K := by
    unfold polyBound; dsimp [a]; push_cast; rw [mul_assoc, ← mul_pow]; gcongr
  let S := (2:ℝ)^((C:ℝ)*b/d)
  have hS : 1 ≤ S := Real.one_le_rpow (by norm_num) (by positivity)
  have hbK := one_le_pow₀ hb' (n := K)
  have hfac : polyBound K l + T + T*S ≤ ((c:ℝ)*(b:ℝ)^K)*S := by
    dsimp [c]; push_cast
    have ha : 0 ≤ (a:ℝ)*(b:ℝ)^K := by positivity
    have ht : (T:ℝ) ≤ T*(b:ℝ)^K := le_mul_of_one_le_right (by positivity) hbK
    calc
      _ ≤ (((a:ℝ)*(b:ℝ)^K+T*(b:ℝ)^K)*S)+T*(b:ℝ)^K*S :=
        add_le_add ((add_le_add hp ht).trans (le_mul_of_one_le_right (by positivity) hS))
          (mul_le_mul_of_nonneg_right ht (by positivity))
      _ = _ := by ring
  have hs : 1 ≤ Real.sqrt b := by simpa using Real.sqrt_le_sqrt hb'
  have hc : (c:ℝ) ≤ (2:ℝ)^((c:ℝ)*Real.sqrt b) := by
    calc
      _ ≤ (2:ℝ)^(c:ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := c)).le
      _ = (2:ℝ)^(c:ℝ) := (Real.rpow_natCast ..).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_mul_of_one_le_right (by positivity) hs)
  have hsK : (b:ℝ)^K ≤ (2:ℝ)^((4*Real.sqrt b)*(K:ℝ)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    gcongr; exact pow_control hb'
  have hscale : Real.sqrt b * d ≤ 2*b := by
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ b),
      mul_le_mul_of_nonneg_left hds (Real.sqrt_nonneg (b:ℝ))]
  have hD : (c:ℝ)*Real.sqrt b + (4*Real.sqrt b)*K ≤ ((2*(c+4*K):ℕ):ℝ)*b/d := by
    apply (le_div_iff₀ hd).mpr; push_cast
    nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ (c:ℝ)+4*K by positivity)]
  have hh := mul_le_mul hc hsK (by positivity) (by positivity)
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hh
  calc
    _ ≤ _ := hfac
    _ ≤ (2:ℝ)^(((2*(c+4*K):ℕ):ℝ)*b/d) * S := mul_le_mul_of_nonneg_right
      (hh.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hD)) (by positivity)
    _ = _ := by dsimp [S]; rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; push_cast; ring

theorem resources (K T C : ℕ) : ∃ D, ∀ b l, 2 ≤ b → l ≤ 50*(b+1) →
    polyBound K l + T + T * mainTimeBound C b ≤ mainTimeBound D b ∧
    polyBound K l + T + T * mainSpaceBound C b ≤ mainSpaceBound D b := by
  obtain ⟨D,H⟩ := absorb K T
  refine ⟨C+D,fun b l hb hl => ?_⟩
  have hs := denoms (b := (b:ℝ)) (by exact_mod_cast hb)
  exact ⟨H b l C hb hl _ hs.1.1 hs.1.2,H b l C hb hl _ hs.2.1 hs.2.2⟩

end DetDLP.w2_bounds

set_option autoImplicit false
set_option maxHeartbeats 3500000

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
  OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∃ (M_sw : PrimitiveMachine) (out_sw : Fin M_sw.tapeCount) (C_sw : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              RunsWithin M_sw out_sw (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_sw (bitLen p)) (mainSpaceBound C_sw (bitLen p))) →
    (∃ (M_ec : PrimitiveMachine) (out_ec : Fin M_ec.tapeCount) (C_ec : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              RunsWithin M_ec out_ec (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_ec (bitLen p)) (mainSpaceBound C_ec (bitLen p))) := by
  rintro ⟨B,o,C,hB⟩
  obtain ⟨A,i,K,hA⟩ := PolyTBridge.polyT_listBool_runsWithin w2_codec.pre w2_codec.pre_poly
  let T := A.tapeCount+B.tapeCount+1
  obtain ⟨D,hD⟩ := w2_bounds.resources K T C
  refine ⟨w2_pipeline.pipeline A B i, (w2_pipeline.wire A B i).tape o, D, ?_⟩
  intro p fp hp E hE
  dsimp only
  letI : Fintype E.toAffine.Point := ecPointFintype E
  intro hr P Q hP
  have small (k : ℕ) (hk : 0 < k) (hk' : k < p) : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hk hk'
  have h6 : (6 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (small 2 (by decide) (by omega)) (small 3 (by decide) hp) using 1 <;> norm_num
  let J := w2_algebra.short E
  letI : J.IsElliptic := w2_algebra.elliptic E h6
  letI : Fintype J.toAffine.Point := ecPointFintype J
  let e : E.toAffine.Point ≃+ J.toAffine.Point := w2_algebra.equiv E h6
  have hc : Fintype.card J.toAffine.Point = Fintype.card E.toAffine.Point := Fintype.card_congr e.symm.toEquiv
  have hj : (Fintype.card J.toAffine.Point).Prime := by rw [hc]; exact hr
  have ho : addOrderOf (e P) = Fintype.card J.toAffine.Point :=
    (e.addOrderOf_eq P).trans (hP.trans hc.symm)
  have hb := @hB p fp hp J (inferInstance : J.IsElliptic) rfl rfl rfl
  obtain ⟨x,hx,he,hrun⟩ := hb hj (e P) (e Q) ho
  refine ⟨x, hx.trans_le hc.le, e.injective (by rwa [map_nsmul]), ?_⟩
  let raw := encodeECDLPInput p E P Q
  have ha := hA raw
  rw [show w2_codec.pre raw = encodeECDLPInput p J (e P) (e Q) from w2_codec.encoded E h6 P Q] at ha
  have run := w2_pipeline.run ha hrun
  have hp' : (2:ℕ) ≤ bitLen p := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by simpa using (show 2 < p by omega))
  obtain ⟨ht,hs⟩ := hD (bitLen p) raw.length hp' (w2_bounds.inputLen E P Q)
  have ht0 : 0 ≤ mainTimeBound C (bitLen p) := by unfold mainTimeBound; positivity
  have hs0 : 0 ≤ mainSpaceBound C (bitLen p) := by unfold mainSpaceBound; positivity
  have hT : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by dsimp [T]; omega)
  have hN : ((A.tapeCount+B.tapeCount:ℕ):ℝ) ≤ T := by exact_mod_cast (show _ ≤ T from Nat.le_succ _)
  have hB' : (B.tapeCount:ℝ) ≤ T := by exact_mod_cast (show B.tapeCount ≤ T by dsimp [T]; omega)
  apply MachineComposition.runsWithin_mono run _ _
  · exact le_trans (by linarith [mul_le_mul_of_nonneg_right hT ht0]) ht
  · exact le_trans (add_le_add (add_le_add_right hB' _) (mul_le_mul_of_nonneg_right hN hs0)) hs

#print axioms solution
