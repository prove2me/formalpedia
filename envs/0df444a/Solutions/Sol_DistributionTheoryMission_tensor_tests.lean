-- Prove2me | solution 1 for DistributionTheoryMission.tensor_tests
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T16:25:05.6034+00:00
-- url     : https://prove2.me/submissions/0e3bb0fe-a24b-4f3f-8781-0bd7e8f3cd22

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_KernelTargets

set_option autoImplicit true
open ComputableAnalysis ComputableDistributions

namespace TensorAux

open RawLimit

theorem rat_mul_corner (ε a c : Rat) (hε : 0 ≤ ε) :
    (a - ε) * c ≥ a * c - ε * qabs c ∧ (a + ε) * c ≤ a * c + ε * qabs c ∧
    (a - ε) * c ≤ a * c + ε * qabs c ∧ (a + ε) * c ≥ a * c - ε * qabs c := by
  have h1 : ε * (-qabs c) ≤ ε * c := Rat.mul_le_mul_of_nonneg_left (neg_qabs_le_self c) hε
  have h2 : ε * c ≤ ε * qabs c := Rat.mul_le_mul_of_nonneg_left (self_le_qabs c) hε
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem product_expand_sub (D C : QInterval) (ε : Rat) (hε : 0 ≤ ε) :
    (QBox.mulRealInterval (D.lo - ε) (D.hi + ε) C.lo C.hi).lo ≥
      (QBox.mulRealInterval D.lo D.hi C.lo C.hi).lo - ε * (qabs C.lo + qabs C.hi) ∧
    (QBox.mulRealInterval (D.lo - ε) (D.hi + ε) C.lo C.hi).hi ≤
      (QBox.mulRealInterval D.lo D.hi C.lo C.hi).hi + ε * (qabs C.lo + qabs C.hi) := by
  have hc := rat_mul_corner ε D.lo C.lo hε
  have hc2 := rat_mul_corner ε D.lo C.hi hε
  have hd := rat_mul_corner ε D.hi C.lo hε
  have hd2 := rat_mul_corner ε D.hi C.hi hε
  have e1 : 0 ≤ ε * qabs C.lo := Rat.mul_nonneg hε (qabs_nonneg _)
  have e2 : 0 ≤ ε * qabs C.hi := Rat.mul_nonneg hε (qabs_nonneg _)
  have key : ε * (qabs C.lo + qabs C.hi) = ε * qabs C.lo + ε * qabs C.hi := by grind
  rw [key]
  simp only [QBox.mulRealInterval, min4, max4, minRat, maxRat2]
  constructor <;> grind


theorem tendsTo_mul_const {u : Nat → RealCompute} {d c : RealCompute}
    (h : TendsTo u d) (hc : c.Valid) :
    TendsTo (fun n => RealCompute.mul (u n) c) (RealCompute.mul d c) := by
  refine ⟨RealCompute.mul_valid h.1 hc, fun n => RealCompute.mul_valid (h.2.1 n) hc, ?_⟩
  intro m eps
  let C := c.compute m
  let K : Rat := qabs C.lo + qabs C.hi + 1
  have hK : 0 < K := by
    have := qabs_nonneg C.lo
    have := qabs_nonneg C.hi
    grind
  let eps' : QPos := ⟨eps.val / K, by
    have := eps.property
    rw [Rat.div_def]; exact Rat.mul_pos this (Rat.inv_pos.2 hK)⟩
  obtain ⟨N, hN⟩ := h.2.2 m eps'
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 := RealIntervalImage.mul (h.2.1 n) hc h1 (RealIntervalImage.current hc m)
  refine RealIntervalImage.weaken h2 ?_
  have hε : 0 ≤ eps'.val := Rat.le_of_lt eps'.property
  have hb := product_expand_sub (d.compute m) C eps'.val hε
  have hkey : eps'.val * (qabs C.lo + qabs C.hi) ≤ eps.val := by
    have hepsK : eps'.val * K = eps.val := by
      show eps.val / K * K = eps.val
      exact Rat.div_mul_cancel (Rat.ne_of_gt hK)
    have := Rat.mul_le_mul_of_nonneg_left (show qabs C.lo + qabs C.hi ≤ K by grind) hε
    grind
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · simp only [QInterval.expand, RealCompute.mul, RealCompute.mulCompute, RealIntervalImage.product]
    grind
  · simp only [QInterval.expand, RealCompute.mul, RealCompute.mulCompute, RealIntervalImage.product]
    grind


open RealApproximationOrder in
theorem secant_mul_equiv (f : Rat → RealCompute) (c : RealCompute) (a b : Rat)
    (hfa : (f a).Valid) (hfb : (f b).Valid) (hc : c.Valid) :
    (BracketDerivative.secant (fun r => RealCompute.mul (f r) c) a b).Equiv
      (RealCompute.mul (BracketDerivative.secant f a b) c) := by
  have := arithmetic_identity
    (scale (1/(b-a)) (sub (ComputableCoefficient.Value.mul (parameter (f b) hfb) (parameter c hc))
      (ComputableCoefficient.Value.mul (parameter (f a) hfa) (parameter c hc))))
    (ComputableCoefficient.Value.mul (scale (1/(b-a)) (sub (parameter (f b) hfb) (parameter (f a) hfa)))
      (parameter c hc))
    (by
      intro s
      simp only [scale, sub, ComputableCoefficient.Value.mul, parameter, ComputableCoefficient.Value.parameter]
      grind)
  exact this

theorem hasDerivative_mul_const {domain : Rat → Prop} {f : Rat → RealCompute}
    {x d c : RealCompute} (h : BracketDerivative.HasDerivativeAt domain f x d)
    (hc : c.Valid) :
    BracketDerivative.HasDerivativeAt domain (fun r => RealCompute.mul (f r) c) x
      (RealCompute.mul d c) := by
  have hv : ∀ r, domain r → (RealCompute.mul (f r) c).Valid :=
    fun r hr => RealCompute.mul_valid (h.2.2.1 r hr) hc
  refine ⟨h.1, RealCompute.mul_valid h.2.1 hc, hv, h.2.2.2.1, ?_⟩
  intro A hA
  apply RawLimit.parametrizedLimit_iff.mpr
  have hT := tendsTo_mul_const (RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)) hc
  apply RawLimit.congr_sequence hT (BracketDerivative.secants_valid hv hA)
  intro n
  have ha := hA.2.2.2 n
  have hlo := ha.2 _ (Rat.le_refl) (Rat.le_of_lt ha.1)
  have hhi := ha.2 _ (Rat.le_of_lt ha.1) (Rat.le_refl)
  exact RealCompute.equiv_symm
    (secant_mul_equiv f c _ _ (h.2.2.1 _ hlo) (h.2.2.1 _ hhi) hc)

open RealApproximationOrder in
theorem mul_comm_equiv (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.mul x y).Equiv (RealCompute.mul y x) := by
  have := arithmetic_identity
    (ComputableCoefficient.Value.mul (parameter x hx) (parameter y hy))
    (ComputableCoefficient.Value.mul (parameter y hy) (parameter x hx))
    (by
      intro s
      simp only [ComputableCoefficient.Value.mul, parameter, ComputableCoefficient.Value.parameter]
      grind)
  exact this

theorem hasDerivative_const_mul {domain : Rat → Prop} {f : Rat → RealCompute}
    {x d c : RealCompute} (h : BracketDerivative.HasDerivativeAt domain f x d)
    (hc : c.Valid) :
    BracketDerivative.HasDerivativeAt domain (fun r => RealCompute.mul c (f r)) x
      (RealCompute.mul c d) := by
  have h1 := hasDerivative_mul_const h hc
  have h2 := BracketDerivative.congr_function h1
    (fun r hr => RealCompute.mul_valid hc (h.2.2.1 r hr))
    (fun r hr => mul_comm_equiv _ _ (h.2.2.1 r hr) hc)
  exact (BracketDerivative.congr_value h2 (RealCompute.mul_valid hc h.2.1)
    (mul_comm_equiv _ _ h.2.1 hc))


open RealApproximationOrder in
theorem ofRat_zero_valid : (RealCompute.ofRat (0:Rat)).Valid := RealCompute.ofRat_valid 0

open RealApproximationOrder in
theorem small_of_inInterval {x : RealCompute} (hx : x.Valid) {B : Rat}
    (h : InInterval x {lo := -B, hi := B}) : Small (parameter x hx) B := h

open RealApproximationOrder in
theorem small_of_equiv_zero {x : RealCompute} (hx : x.Valid)
    (h : x.Equiv (RealCompute.ofRat 0)) {B : Rat} (hB : 0 ≤ B) :
    Small (parameter x hx) B := by
  apply small_of_inInterval
  have h0 := RealIntervalImage.current (ofRat_zero_valid) 0
  have h1 : InInterval (RealCompute.ofRat 0) {lo := -B, hi := B} :=
    RealIntervalImage.weaken h0 ⟨by change -B ≤ 0; grind, by change 0 ≤ B; exact hB⟩
  exact RawLimit.inInterval_congr (I := {lo := -B, hi := B})
    (ofRat_zero_valid) hx (RealCompute.equiv_symm h) h1

open RealApproximationOrder in
theorem small_of_sub_equiv_zero {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (h : y.Equiv (RealCompute.ofRat 0)) {B : Rat}
    (hs : Small (sub (parameter x hx) (parameter y hy)) B) : Small (parameter x hx) B := by
  have e1 : (RealCompute.sub x y).Equiv (RealCompute.sub x (RealCompute.ofRat 0)) :=
    RealCompute.sub_equiv hx hx hy (ofRat_zero_valid) (RealCompute.equiv_refl x hx) h
  have e2 : (RealCompute.sub x (RealCompute.ofRat 0)).Equiv x := by
    have := arithmetic_identity (sub (parameter x hx) (ComputableCoefficient.Value.rational 0))
      (parameter x hx) (by
        intro s
        simp only [sub, parameter, ComputableCoefficient.Value.parameter,
          ComputableCoefficient.Value.rational]
        grind)
    exact this
  have e3 := RealCompute.equiv_trans (RealCompute.sub_valid hx hy)
    (RealCompute.sub_valid hx (ofRat_zero_valid)) hx e1 e2
  exact Small.congr hs e3

open RealApproximationOrder in
theorem small_bound_zero_dim (f : RealCompute) (hf : f.Valid) :
    ∃ B : Rat, 0 ≤ B ∧ Small (parameter f hf) B := by
  refine ⟨qabs (f.compute 0).lo + qabs (f.compute 0).hi,
    Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _), ?_⟩
  apply small_of_inInterval
  refine RealIntervalImage.weaken (RealIntervalImage.current hf 0) ⟨?_, ?_⟩
  · have := neg_qabs_le_self (f.compute 0).lo
    have := qabs_nonneg (f.compute 0).hi
    change -(qabs (f.compute 0).lo + qabs (f.compute 0).hi) ≤ (f.compute 0).lo
    grind
  · have := self_le_qabs (f.compute 0).hi
    have := qabs_nonneg (f.compute 0).lo
    change (f.compute 0).hi ≤ qabs (f.compute 0).lo + qabs (f.compute 0).hi
    grind


open RealApproximationOrder in
theorem testFunction_uniform_bound {d : Nat} (φ : TestFunction d) (α : MultiIndex d) :
    ∃ M : Rat, 0 ≤ M ∧ ∀ x, Small (parameter (φ.derivative α x) (φ.derivative_valid α x)) M := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · obtain ⟨B, hB, hS⟩ := small_bound_zero_dim (φ.derivative α (origin 0)) (φ.derivative_valid α _)
    refine ⟨B, hB, fun x => ?_⟩
    have : x = origin 0 := funext fun i => i.elim0
    subst this
    exact hS
  · let j0 : Fin d := ⟨0, hpos⟩
    let δ : Rat := φ.support.upper j0 - φ.support.lower j0 + 1
    have hδ : 0 ≤ δ := by
      have := φ.support.ordered j0
      grind
    let L := φ.derivativeLipschitz α
    have hL := φ.derivativeLipschitz_nonneg α
    have hM : 0 ≤ L * δ := Rat.mul_nonneg hL hδ
    refine ⟨L * δ, hM, fun x => ?_⟩
    by_cases hx : φ.support.Contains x
    · let y := replaceCoordinate x j0 (φ.support.lower j0 - 1)
      have hy : ¬ φ.support.Contains y := by
        intro h
        have := (h j0).1
        simp only [y, replaceCoordinate, if_true] at this
        grind
      have hctrl := φ.derivative_control α x y δ hδ (by
        intro i
        by_cases hi : i = j0
        · subst hi
          have h1 := (hx j0).1
          have h2 := (hx j0).2
          simp only [y, replaceCoordinate, if_true]
          constructor <;> grind
        · simp only [y, replaceCoordinate, hi, if_false]
          constructor <;> grind)
      exact small_of_sub_equiv_zero _ _ (φ.derivative_vanishes_off_support α y hy) hctrl
    · exact small_of_equiv_zero _ (φ.derivative_vanishes_off_support α x hx) hM


def tensorDeriv {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n)
    (α : MultiIndex (m + n)) (z : QPoint (m + n)) : RealCompute :=
  RealCompute.mul
    (φ.derivative (fun i => α (Fin.castAdd n i)) (fun i => z (Fin.castAdd n i)))
    (ψ.derivative (fun j => α (Fin.natAdd m j)) (fun j => z (Fin.natAdd m j)))

theorem tensorDeriv_valid {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n)
    (α : MultiIndex (m + n)) (z : QPoint (m + n)) : (tensorDeriv φ ψ α z).Valid :=
  RealCompute.mul_valid (φ.derivative_valid _ _) (ψ.derivative_valid _ _)

def tensorBox {m n : Nat} (A : RationalBox m) (B : RationalBox n) : RationalBox (m + n) where
  lower := fun k => Fin.addCases (motive := fun _ => Rat) A.lower B.lower k
  upper := fun k => Fin.addCases (motive := fun _ => Rat) A.upper B.upper k
  ordered := by
    intro k
    induction k using Fin.addCases with
    | left i => simpa using A.ordered i
    | right j => simpa using B.ordered j

theorem tensorBox_contains {m n : Nat} (A : RationalBox m) (B : RationalBox n)
    (z : QPoint (m + n)) (hA : A.Contains (fun i => z (Fin.castAdd n i)))
    (hB : B.Contains (fun j => z (Fin.natAdd m j))) : (tensorBox A B).Contains z := by
  intro k
  induction k using Fin.addCases with
  | left i => simpa [tensorBox] using hA i
  | right j => simpa [tensorBox] using hB j

theorem mul_left_zero {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (h : x.Equiv (RealCompute.ofRat 0)) : (RealCompute.mul x y).Equiv (RealCompute.ofRat 0) := by
  have e1 := RealCompute.mul_equiv hx ofRat_zero_valid hy hy h (RealCompute.equiv_refl y hy)
  have e2 : (RealCompute.mul (RealCompute.ofRat 0) y).Equiv (RealCompute.ofRat 0) := by
    have := RealApproximationOrder.arithmetic_identity
      (ComputableCoefficient.Value.mul (ComputableCoefficient.Value.rational 0)
        (RealApproximationOrder.parameter y hy)) (ComputableCoefficient.Value.rational 0)
      (by
        intro s
        simp only [ComputableCoefficient.Value.mul, ComputableCoefficient.Value.rational]
        grind)
    exact this
  exact RealCompute.equiv_trans (RealCompute.mul_valid hx hy)
    (RealCompute.mul_valid ofRat_zero_valid hy) ofRat_zero_valid e1 e2

theorem mul_right_zero {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (h : y.Equiv (RealCompute.ofRat 0)) : (RealCompute.mul x y).Equiv (RealCompute.ofRat 0) :=
  RealCompute.equiv_trans (RealCompute.mul_valid hx hy) (RealCompute.mul_valid hy hx)
    ofRat_zero_valid (mul_comm_equiv x y hx hy) (mul_left_zero hy hx h)

theorem tensorDeriv_vanishes {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n)
    (α : MultiIndex (m + n)) (z : QPoint (m + n))
    (hz : ¬ (tensorBox φ.support ψ.support).Contains z) :
    (tensorDeriv φ ψ α z).Equiv (RealCompute.ofRat 0) := by
  by_cases hA : φ.support.Contains (fun i => z (Fin.castAdd n i))
  · have hB : ¬ ψ.support.Contains (fun j => z (Fin.natAdd m j)) :=
      fun hB => hz (tensorBox_contains _ _ z hA hB)
    exact mul_right_zero (φ.derivative_valid _ _) (ψ.derivative_valid _ _)
      (ψ.derivative_vanishes_off_support _ _ hB)
  · exact mul_left_zero (φ.derivative_valid _ _) (ψ.derivative_valid _ _)
      (φ.derivative_vanishes_off_support _ _ hA)


open RealApproximationOrder ComputableCoefficient in
theorem small_prod_diff (Fx Fy Gx Gy : RealCompute) (hFx : Fx.Valid) (hFy : Fy.Valid)
    (hGx : Gx.Valid) (hGy : Gy.Valid) (M1 M2 B1 B2 : Rat)
    (h1 : Small (parameter Fx hFx) M1) (h2 : Small (parameter Gy hGy) M2)
    (c1 : Small (sub (parameter Fx hFx) (parameter Fy hFy)) B1)
    (c2 : Small (sub (parameter Gx hGx) (parameter Gy hGy)) B2) :
    Small (sub (parameter (RealCompute.mul Fx Gx) (RealCompute.mul_valid hFx hGx))
      (parameter (RealCompute.mul Fy Gy) (RealCompute.mul_valid hFy hGy))) (M1 * B2 + B1 * M2) := by
  have hS := Small.add (Small.mul h1 c2) (Small.mul c1 h2)
  refine Small.congr hS ?_
  exact arithmetic_identity
    (Value.add (Value.mul (parameter Fx hFx) (sub (parameter Gx hGx) (parameter Gy hGy)))
      (Value.mul (sub (parameter Fx hFx) (parameter Fy hFy)) (parameter Gy hGy)))
    (sub (Value.mul (parameter Fx hFx) (parameter Gx hGx))
      (Value.mul (parameter Fy hFy) (parameter Gy hGy)))
    (by
      intro s
      simp only [Value.add, Value.mul, sub, parameter, Value.parameter]
      grind)


theorem my_castAdd_inj {m : Nat} (n : Nat) (k j : Fin m) :
    Fin.castAdd n k = Fin.castAdd n j ↔ k = j :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa using this), fun h => by rw [h]⟩

theorem my_natAdd_inj (m : Nat) {n : Nat} (k j : Fin n) :
    Fin.natAdd m k = Fin.natAdd m j ↔ k = j :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega), fun h => by rw [h]⟩

theorem castAdd_replace {m n : Nat} (z : QPoint (m + n)) (j : Fin m) (r : Rat) :
    (fun k : Fin m => replaceCoordinate z (Fin.castAdd n j) r (Fin.castAdd n k)) =
      replaceCoordinate (fun k => z (Fin.castAdd n k)) j r := by
  funext k
  simp only [replaceCoordinate, my_castAdd_inj]

theorem natAdd_replace_castAdd {m n : Nat} (z : QPoint (m + n)) (j : Fin m) (r : Rat) :
    (fun k : Fin n => replaceCoordinate z (Fin.castAdd n j) r (Fin.natAdd m k)) =
      fun k => z (Fin.natAdd m k) := by
  funext k
  have : Fin.natAdd m k ≠ Fin.castAdd n j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := j.isLt
    omega
  simp only [replaceCoordinate, if_neg this]

theorem natAdd_replace {m n : Nat} (z : QPoint (m + n)) (j : Fin n) (r : Rat) :
    (fun k : Fin n => replaceCoordinate z (Fin.natAdd m j) r (Fin.natAdd m k)) =
      replaceCoordinate (fun k => z (Fin.natAdd m k)) j r := by
  funext k
  simp only [replaceCoordinate, my_natAdd_inj]

theorem castAdd_replace_natAdd {m n : Nat} (z : QPoint (m + n)) (j : Fin n) (r : Rat) :
    (fun k : Fin m => replaceCoordinate z (Fin.natAdd m j) r (Fin.castAdd n k)) =
      fun k => z (Fin.castAdd n k) := by
  funext k
  have : Fin.castAdd n k ≠ Fin.natAdd m j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := k.isLt
    omega
  simp only [replaceCoordinate, if_neg this]

theorem castAdd_incr {m n : Nat} (α : MultiIndex (m + n)) (j : Fin m) :
    (fun k : Fin m => incrementIndex α (Fin.castAdd n j) (Fin.castAdd n k)) =
      incrementIndex (fun k => α (Fin.castAdd n k)) j := by
  funext k
  simp only [incrementIndex, my_castAdd_inj]

theorem natAdd_incr_castAdd {m n : Nat} (α : MultiIndex (m + n)) (j : Fin m) :
    (fun k : Fin n => incrementIndex α (Fin.castAdd n j) (Fin.natAdd m k)) =
      fun k => α (Fin.natAdd m k) := by
  funext k
  have : Fin.natAdd m k ≠ Fin.castAdd n j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := j.isLt
    omega
  simp only [incrementIndex, if_neg this, Nat.add_zero]

theorem natAdd_incr {m n : Nat} (α : MultiIndex (m + n)) (j : Fin n) :
    (fun k : Fin n => incrementIndex α (Fin.natAdd m j) (Fin.natAdd m k)) =
      incrementIndex (fun k => α (Fin.natAdd m k)) j := by
  funext k
  simp only [incrementIndex, my_natAdd_inj]

theorem castAdd_incr_natAdd {m n : Nat} (α : MultiIndex (m + n)) (j : Fin n) :
    (fun k : Fin m => incrementIndex α (Fin.natAdd m j) (Fin.castAdd n k)) =
      fun k => α (Fin.castAdd n k) := by
  funext k
  have : Fin.castAdd n k ≠ Fin.natAdd m j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := k.isLt
    omega
  simp only [incrementIndex, if_neg this, Nat.add_zero]

theorem tensor_partial {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n)
    (α : MultiIndex (m + n)) (i : Fin (m + n)) (z : QPoint (m + n)) :
    BracketDerivative.HasDerivativeAt (fun _ => True)
      (fun r => tensorDeriv φ ψ α (replaceCoordinate z i r))
      (RealCompute.ofRat (z i)) (tensorDeriv φ ψ (incrementIndex α i) z) := by
  induction i using Fin.addCases with
  | left j =>
    have h := hasDerivative_mul_const
      (φ.partialDerivative (fun k => α (Fin.castAdd n k)) j (fun k => z (Fin.castAdd n k)))
      (ψ.derivative_valid (fun k => α (Fin.natAdd m k)) (fun k => z (Fin.natAdd m k)))
    simp only [tensorDeriv, castAdd_replace, natAdd_replace_castAdd, castAdd_incr,
      natAdd_incr_castAdd]
    exact h
  | right j =>
    have h := hasDerivative_const_mul
      (ψ.partialDerivative (fun k => α (Fin.natAdd m k)) j (fun k => z (Fin.natAdd m k)))
      (φ.derivative_valid (fun k => α (Fin.castAdd n k)) (fun k => z (Fin.castAdd n k)))
    simp only [tensorDeriv, natAdd_replace, castAdd_replace_natAdd, natAdd_incr,
      castAdd_incr_natAdd]
    exact h


open RealApproximationOrder in
noncomputable def tensorTest {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n) :
    TestFunction (m + n) where
  derivative := tensorDeriv φ ψ
  derivative_valid := tensorDeriv_valid φ ψ
  support := tensorBox φ.support ψ.support
  derivative_vanishes_off_support := fun α z hz => tensorDeriv_vanishes φ ψ α z hz
  derivativeLipschitz := fun α =>
    (testFunction_uniform_bound φ (fun i => α (Fin.castAdd n i))).choose *
        ψ.derivativeLipschitz (fun j => α (Fin.natAdd m j)) +
      φ.derivativeLipschitz (fun i => α (Fin.castAdd n i)) *
        (testFunction_uniform_bound ψ (fun j => α (Fin.natAdd m j))).choose
  derivativeLipschitz_nonneg := fun α => by
    have a := (testFunction_uniform_bound φ (fun i => α (Fin.castAdd n i))).choose_spec.1
    have b := (testFunction_uniform_bound ψ (fun j => α (Fin.natAdd m j))).choose_spec.1
    have c := φ.derivativeLipschitz_nonneg (fun i => α (Fin.castAdd n i))
    have d := ψ.derivativeLipschitz_nonneg (fun j => α (Fin.natAdd m j))
    exact Rat.add_nonneg (Rat.mul_nonneg a d) (Rat.mul_nonneg c b)
  derivative_control := fun α z y δ hδ hclose => by
    have c1 := φ.derivative_control (fun i => α (Fin.castAdd n i)) (fun i => z (Fin.castAdd n i))
      (fun i => y (Fin.castAdd n i)) δ hδ (fun i => hclose _)
    have c2 := ψ.derivative_control (fun j => α (Fin.natAdd m j)) (fun j => z (Fin.natAdd m j))
      (fun j => y (Fin.natAdd m j)) δ hδ (fun j => hclose _)
    have h1 := (testFunction_uniform_bound φ (fun i => α (Fin.castAdd n i))).choose_spec.2
      (fun i => z (Fin.castAdd n i))
    have h2 := (testFunction_uniform_bound ψ (fun j => α (Fin.natAdd m j))).choose_spec.2
      (fun j => y (Fin.natAdd m j))
    have := small_prod_diff _ _ _ _ (φ.derivative_valid _ _) (φ.derivative_valid _ _)
      (ψ.derivative_valid _ _) (ψ.derivative_valid _ _) _ _ _ _ h1 h2 c1 c2
    refine Small.mono this ?_
    grind
  partialDerivative := fun α i z => tensor_partial φ ψ α i z

end TensorAux

open TensorAux in
theorem solution : ComputableDistributions.TensorTestsExistTarget := by
  intro m n φ ψ
  refine ⟨tensorTest φ ψ, fun α z => ?_⟩
  exact RealCompute.equiv_refl _ (tensorDeriv_valid φ ψ α z)
