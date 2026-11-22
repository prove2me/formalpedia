-- Prove2me | solution 1 for ComputableDistributionsWaveMission.distributional_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T16:59:20.870592+00:00
-- url     : https://prove2.me/submissions/9b766ccc-773c-4193-b3f3-15e4a336c030

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_MissionTargets
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueArithmetic

open ComputableAnalysis ComputableDistributions

namespace DistributionalDerivativeAux

open RealComputeQuotient in
theorem neg_add_equiv {X a b : RealCompute} (hX : X.Valid) (ha : a.Valid) (hb : b.Valid)
    (h : X.Equiv (RealCompute.add a b)) :
    (RealCompute.neg X).Equiv
      (RealCompute.add (RealCompute.neg a) (RealCompute.neg b)) := by
  have q : ofRaw X hX = ofRaw a ha + ofRaw b hb :=
    ofRaw_eq_ofRaw (hy := RealCompute.add_valid ha hb) h
  apply equiv_of_ofRaw_eq (hx := RealCompute.neg_valid hX)
    (hy := RealCompute.add_valid (RealCompute.neg_valid ha) (RealCompute.neg_valid hb))
  show -(ofRaw X hX) = -(ofRaw a ha) + -(ofRaw b hb)
  rw [q]
  grind

open RealComputeQuotient in
theorem neg_mul_equiv {X r a : RealCompute} (hX : X.Valid) (hr : r.Valid) (ha : a.Valid)
    (h : X.Equiv (RealCompute.mul r a)) :
    (RealCompute.neg X).Equiv (RealCompute.mul r (RealCompute.neg a)) := by
  have q : ofRaw X hX = ofRaw r hr * ofRaw a ha :=
    ofRaw_eq_ofRaw (hy := RealCompute.mul_valid hr ha) h
  apply equiv_of_ofRaw_eq (hx := RealCompute.neg_valid hX)
    (hy := RealCompute.mul_valid hr (RealCompute.neg_valid ha))
  show -(ofRaw X hX) = ofRaw r hr * -(ofRaw a ha)
  rw [q]
  grind

theorem v0 : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0

open RealComputeQuotient in
theorem neg_zero_equiv {X : RealCompute} (hX : X.Valid)
    (h : X.Equiv (RealCompute.ofRat 0)) :
    (RealCompute.neg X).Equiv (RealCompute.ofRat 0) := by
  have q : ofRaw X hX = ofRaw (RealCompute.ofRat 0) v0 := ofRaw_eq_ofRaw h
  have e : ofRaw (-X) (RealCompute.neg_valid hX) = -(ofRaw X hX) := rfl
  have z : ofRaw (RealCompute.ofRat 0) v0 = (0 : Value) := rfl
  apply equiv_of_ofRaw_eq (hx := RealCompute.neg_valid hX) (hy := v0)
  rw [e, q, z]
  grind

theorem small_neg {a : RealCompute} (ha : a.Valid) (hna : (RealCompute.neg a).Valid)
    {B : Rat} (h : RealApproximationOrder.Small (RealApproximationOrder.parameter a ha) B) :
    RealApproximationOrder.Small (RealApproximationOrder.parameter (RealCompute.neg a) hna) B := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro n m
    have := h2 m n
    change (a.compute m).lo ≤ B at this
    change -B ≤ -(a.compute m).lo
    grind
  · intro n m
    have := h1 m n
    change -B ≤ (a.compute n).hi at this
    change -(a.compute n).hi ≤ B
    grind

theorem order_increment : ∀ {d : Nat} (alpha : MultiIndex d) (i : Fin d),
    multiIndexOrder (incrementIndex alpha i) = multiIndexOrder alpha + 1
  | 0, _, i => i.elim0
  | d + 1, alpha, i => by
    show multiIndexOrder (fun j : Fin d => incrementIndex alpha i j.castSucc) +
        incrementIndex alpha i (Fin.last d) =
      multiIndexOrder (fun j : Fin d => alpha j.castSucc) + alpha (Fin.last d) + 1
    induction i using Fin.lastCases with
    | cast k =>
      have h1 : (fun j : Fin d => incrementIndex alpha k.castSucc j.castSucc) =
          incrementIndex (fun j : Fin d => alpha j.castSucc) k := by
        funext j
        simp [incrementIndex, Fin.castSucc_inj]
      rw [h1, order_increment]
      have hk := k.isLt
      have h2 : Fin.last d ≠ k.castSucc :=
        Fin.ne_of_val_ne (by simp only [Fin.val_last, Fin.val_castSucc]; omega)
      simp only [incrementIndex, if_neg h2]
      omega
    | last =>
      have h1 : (fun j : Fin d => incrementIndex alpha (Fin.last d) j.castSucc) =
          fun j => alpha j.castSucc := by
        funext j
        have hj := j.isLt
        have h2 : j.castSucc ≠ Fin.last d :=
          Fin.ne_of_val_ne (by simp only [Fin.val_last, Fin.val_castSucc]; omega)
        simp only [incrementIndex, if_neg h2]
        omega
      rw [h1]
      simp [incrementIndex] <;> omega

theorem partial_bounded {d : Nat} (φ : TestFunction d) (i : Fin d) (order : Nat) (bound : Rat)
    (h : φ.DerivativesBoundedBy (order + 1) bound) :
    (φ.coordinatePartial i).DerivativesBoundedBy order bound := by
  intro alpha halpha x
  exact h (incrementIndex alpha i) (by rw [order_increment]; omega) x

theorem secant_zero {f : Rat → RealCompute} {a b : Rat}
    (ha : (f a).Valid) (hb : (f b).Valid)
    (ha0 : (f a).Equiv (RealCompute.ofRat 0)) (hb0 : (f b).Equiv (RealCompute.ofRat 0)) :
    (BracketDerivative.secant f a b).Equiv (RealCompute.ofRat 0) := by
  have h1 : (BracketDerivative.secant f a b).Equiv
      (RealCompute.scaleRat (1/(b-a)) (RealCompute.ofRat 0 - RealCompute.ofRat 0)) :=
    RealCompute.scaleRat_equiv (RealCompute.sub_equiv hb v0 ha v0 hb0 ha0)
  have h2 : (RealCompute.scaleRat (1/(b-a))
      (RealCompute.ofRat 0 - RealCompute.ofRat 0)).Equiv (RealCompute.ofRat 0) := by
    intro n
    apply (RealCompute.compareAt_overlap_iff _ _ n n).2
    show QInterval.Overlaps (RealCompute.scaleRatCompute _ _ n) _
    unfold RealCompute.scaleRatCompute
    have hz : Rat.sub 0 0 = 0 := by show (0 : Rat) - 0 = 0; grind
    split <;>
      simp [QInterval.Overlaps, RealCompute.ofRat, HSub.hSub, Sub.sub, RealCompute.sub,
        RealCompute.subCompute, hz]
  exact RealCompute.equiv_trans (BracketDerivative.secant_valid ha hb)
    (RealCompute.scaleRat_valid (RealCompute.sub_valid v0 v0)) v0 h1 h2

theorem tendsTo_shiftN {u : Nat → RealCompute} {x : RealCompute} (h : RawLimit.TendsTo u x) :
    ∀ N, RawLimit.TendsTo (fun n => u (n + N)) x
  | 0 => by simpa using h
  | N + 1 => by
    have := RawLimit.shift (tendsTo_shiftN h N)
    simpa [Nat.add_assoc, Nat.add_comm 1 N] using this

/-- Vanishing of the value outside a box passes to every first coordinate
partial: outside the closed box, admissible secant brackets eventually lie in
the region where the test vanishes, so all late secants are zero. -/
theorem partial_supported {d : Nat} (φ : TestFunction d) (B : RationalBox d)
    (hφ : φ.SupportedInBox B) (i : Fin d) : (φ.coordinatePartial i).SupportedInBox B := by
  intro x hx
  have hD := φ.partialDerivative (zeroIndex d) i x
  obtain ⟨_, _, hfv, ⟨A, hA⟩, hlim⟩ :=
    BracketDerivative.hasDerivative_iff_secantLimits.mp hD
  have hT := hlim A hA
  have key : ∃ N, ∀ n, N ≤ n → ∀ r, (A.compute n).lo ≤ r → r ≤ (A.compute n).hi →
      ¬ B.Contains (replaceCoordinate x i r) := by
    have hx' : ∃ j, ¬ (B.lower j ≤ x j ∧ x j ≤ B.upper j) := by
      classical
      exact Classical.byContradiction fun hn => hx (fun j =>
        Classical.byContradiction fun hj => hn ⟨j, hj⟩)
    obtain ⟨j, hj⟩ := hx'
    by_cases hji : j = i
    · subst hji
      have hover : ∀ n, (A.compute n).lo ≤ x j ∧ x j ≤ (A.compute n).hi := by
        intro n
        have := (RealCompute.compareAt_overlap_iff _ _ n n).1 (hA.2.2.1 n)
        exact ⟨this.1, this.2⟩
      by_cases hlow : B.lower j ≤ x j
      · have hup : B.upper j < x j := by grind
        obtain ⟨N, hN⟩ := hA.2.1.2.2 ⟨(x j - B.upper j) / 2, by grind⟩
        refine ⟨N, fun n hn r hr _ hc => ?_⟩
        have hw := hN n hn
        have ho := hover n
        unfold QInterval.width at hw
        have hcj := (hc j).2
        simp only [replaceCoordinate] at hcj
        grind
      · obtain ⟨N, hN⟩ := hA.2.1.2.2 ⟨(B.lower j - x j) / 2, by grind⟩
        refine ⟨N, fun n hn r _ hr hc => ?_⟩
        have hw := hN n hn
        have ho := hover n
        unfold QInterval.width at hw
        have hcj := (hc j).1
        simp only [replaceCoordinate] at hcj
        grind
    · refine ⟨0, fun n _ r _ _ hc => hj ?_⟩
      have := hc j
      simpa only [replaceCoordinate, if_neg hji] using this
  obtain ⟨N, hN⟩ := key
  have hshift := tendsTo_shiftN hT N
  have hzero : RawLimit.TendsTo (fun _ => RealCompute.ofRat 0)
      (φ.derivative (incrementIndex (zeroIndex d) i) x) :=
    RawLimit.congr_sequence hshift (fun _ => RealCompute.ofRat_valid 0) (fun n => by
      have hb := hA.2.2.2 (n + N)
      exact secant_zero (hfv _ trivial) (hfv _ trivial)
        (hφ _ (hN _ (Nat.le_add_left _ _) _ (Rat.le_refl) (Rat.le_of_lt hb.1)))
        (hφ _ (hN _ (Nat.le_add_left _ _) _ (Rat.le_of_lt hb.1) (Rat.le_refl))))
  exact RawLimit.unique hzero (RawLimit.constant _ v0)

theorem partial_equiv {d : Nat} {φ ψ : TestFunction d} (i : Fin d)
    (h : TestFunction.Equivalent φ ψ) :
    TestFunction.Equivalent (φ.coordinatePartial i) (ψ.coordinatePartial i) :=
  fun alpha x => h (incrementIndex alpha i) x

theorem partial_add {d : Nat} (tests : TestFunctionSpace d) (φ ψ : TestFunction d) (i : Fin d) :
    TestFunction.Equivalent ((tests.add φ ψ).coordinatePartial i)
      (tests.add (φ.coordinatePartial i) (ψ.coordinatePartial i)) := by
  intro alpha x
  have hv := RealCompute.add_valid (φ.derivative_valid (incrementIndex alpha i) x)
    (ψ.derivative_valid (incrementIndex alpha i) x)
  exact RealCompute.equiv_trans ((tests.add φ ψ).derivative_valid _ x) hv
    ((tests.add _ _).derivative_valid alpha x)
    (tests.add_derivative φ ψ (incrementIndex alpha i) x)
    (RealCompute.equiv_symm
      (tests.add_derivative (φ.coordinatePartial i) (ψ.coordinatePartial i) alpha x))

theorem partial_scale {d : Nat} (tests : TestFunctionSpace d) (r : RealCompute) (hr : r.Valid)
    (φ : TestFunction d) (i : Fin d) :
    TestFunction.Equivalent ((tests.scale r hr φ).coordinatePartial i)
      (tests.scale r hr (φ.coordinatePartial i)) := by
  intro alpha x
  have hv := RealCompute.mul_valid hr (φ.derivative_valid (incrementIndex alpha i) x)
  exact RealCompute.equiv_trans ((tests.scale r hr φ).derivative_valid _ x) hv
    ((tests.scale r hr _).derivative_valid alpha x)
    (tests.scale_derivative r hr φ (incrementIndex alpha i) x)
    (RealCompute.equiv_symm
      (tests.scale_derivative r hr (φ.coordinatePartial i) alpha x))

theorem partial_zero {d : Nat} (tests : TestFunctionSpace d) (i : Fin d) :
    TestFunction.Equivalent (tests.zero.coordinatePartial i) tests.zero := by
  intro alpha x
  exact RealCompute.equiv_trans (tests.zero.derivative_valid _ x) v0
    (tests.zero.derivative_valid alpha x)
    (tests.zero_derivative (incrementIndex alpha i) x)
    (RealCompute.equiv_symm (tests.zero_derivative alpha x))

/-- The distributional derivative `⟨∂ᵢT, φ⟩ = -⟨T, ∂ᵢφ⟩`. -/
def derivative {d : Nat} {tests : TestFunctionSpace d} (T : Distribution tests) (i : Fin d) :
    Distribution tests where
  action φ := RealCompute.neg (T.action (φ.coordinatePartial i))
  action_linear :=
    { value_valid := fun φ => RealCompute.neg_valid (T.action_valid _)
      respects_test_equiv := fun φ ψ h =>
        RealCompute.neg_equiv (T.action_linear.respects_test_equiv _ _ (partial_equiv i h))
      map_zero := by
        apply neg_zero_equiv (T.action_valid _)
        exact RealCompute.equiv_trans (T.action_valid _) (T.action_valid _) v0
          (T.action_linear.respects_test_equiv _ _ (partial_zero tests i))
          T.action_linear.map_zero
      map_add := fun φ ψ => by
        apply neg_add_equiv (T.action_valid _) (T.action_valid _) (T.action_valid _)
        exact RealCompute.equiv_trans (T.action_valid _) (T.action_valid _)
          (RealCompute.add_valid (T.action_valid _) (T.action_valid _))
          (T.action_linear.respects_test_equiv _ _ (partial_add tests φ ψ i))
          (T.action_linear.map_add _ _)
      map_scale := fun r hr φ => by
        apply neg_mul_equiv (T.action_valid _) hr (T.action_valid _)
        exact RealCompute.equiv_trans (T.action_valid _) (T.action_valid _)
          (RealCompute.mul_valid hr (T.action_valid _))
          (T.action_linear.respects_test_equiv _ _ (partial_scale tests r hr φ i))
          (T.action_linear.map_scale _ _ _) }
  action_continuous := by
    intro B
    obtain ⟨order, C, hC, h⟩ := T.action_continuous B
    refine ⟨order + 1, C, hC, fun φ hφ bound hbound hder => ?_⟩
    exact small_neg (T.action_valid _) _
      (h _ (partial_supported φ B hφ i) bound hbound (partial_bounded φ i order bound hder))

end DistributionalDerivativeAux

theorem solution : ComputableDistributions.DistributionalDerivativeTarget := by
  intro d tests T i
  exact ⟨DistributionalDerivativeAux.derivative T i,
    fun φ => RealCompute.equiv_refl _ (RealCompute.neg_valid (T.action_valid _))⟩
