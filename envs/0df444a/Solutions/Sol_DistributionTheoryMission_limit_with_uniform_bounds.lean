-- Prove2me | solution 1 for DistributionTheoryMission.limit_with_uniform_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T23:52:51.746879+00:00
-- url     : https://prove2.me/submissions/0116ee8f-bad9-4f4a-a319-bb0a6119adb9

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ConvergenceTargets

set_option autoImplicit true
open ComputableAnalysis ComputableDistributions

namespace LimAux

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


theorem tendsTo_add {u v : Nat → RealCompute} {x y : RealCompute}
    (hu : TendsTo u x) (hv : TendsTo v y) :
    TendsTo (fun n => RealCompute.add (u n) (v n)) (RealCompute.add x y) := by
  refine ⟨RealCompute.add_valid hu.1 hv.1,
    fun n => RealCompute.add_valid (hu.2.1 n) (hv.2.1 n), ?_⟩
  intro m eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨N1, h1⟩ := hu.2.2 m half
  obtain ⟨N2, h2⟩ := hv.2.2 m half
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a := h1 n (by omega)
  have b := h2 n (by omega)
  constructor
  · intro i j
    have a1 := a.1 0 j
    have b1 := b.1 0 j
    change (x.compute m).lo - half.val ≤ ((u n).compute j).hi at a1
    change (y.compute m).lo - half.val ≤ ((v n).compute j).hi at b1
    change (x.compute m).lo + (y.compute m).lo - eps.val ≤ ((u n).compute j).hi + ((v n).compute j).hi
    dsimp [half] at a1 b1
    grind only [Rat.div_def]
  · intro i j
    have a1 := a.2 i 0
    have b1 := b.2 i 0
    change ((u n).compute i).lo ≤ (x.compute m).hi + half.val at a1
    change ((v n).compute i).lo ≤ (y.compute m).hi + half.val at b1
    change ((u n).compute i).lo + ((v n).compute i).lo ≤ (x.compute m).hi + (y.compute m).hi + eps.val
    dsimp [half] at a1 b1
    grind only [Rat.div_def]

theorem limit_in_interval {u : Nat → RealCompute} {x : RealCompute} (h : TendsTo u x) (I : QInterval)
    (hb : ∃ N, ∀ n, N≤n → InInterval (u n) I) : InInterval x I := by
  obtain ⟨K,hK⟩ := hb
  constructor
  · intro i j
    by_cases H : I.lo≤(x.compute j).hi
    · exact H
    have HP : 0<(I.lo-(x.compute j).hi)/2 := by grind only
    obtain ⟨N,hN⟩ := h.2.2 j ⟨_,HP⟩
    let n := max N K
    have HU := RealCompute.le_trans (h.2.1 n) (hK n (by dsimp [n]; omega)).1 (hN n (by dsimp [n]; omega)).2 0 0
    change I.lo≤(x.compute j).hi+(I.lo-(x.compute j).hi)/2 at HU
    grind only
  · intro i j
    by_cases H : (x.compute i).lo≤I.hi
    · exact H
    have HP : 0<((x.compute i).lo-I.hi)/2 := by grind only
    obtain ⟨N,hN⟩ := h.2.2 i ⟨_,HP⟩
    let n := max N K
    have HL := RealCompute.le_trans (h.2.1 n) (hN n (by dsimp [n]; omega)).1 (hK n (by dsimp [n]; omega)).2 0 0
    change (x.compute i).lo-((x.compute i).lo-I.hi)/2≤I.hi at HL
    grind only

theorem tendsTo_const_mul {u : Nat → RealCompute} {d c : RealCompute}
    (h : TendsTo u d) (hc : c.Valid) :
    TendsTo (fun n => RealCompute.mul c (u n)) (RealCompute.mul c d) := by
  have h1 := tendsTo_mul_const h hc
  have h2 := congr_sequence h1 (fun n => RealCompute.mul_valid hc (h.2.1 n))
    (fun n => mul_comm_equiv _ _ (h.2.1 n) hc)
  exact congr_target h2 (RealCompute.mul_valid hc h.1) (mul_comm_equiv _ _ h.1 hc)

end LimAux

open LimAux in
theorem solution : ComputableDistributions.DistributionLimitWithUniformBoundsTarget := by
  intro d S u A hB hC
  have hlin : IsLinearAction S A := by
    refine ⟨fun φ => (hC φ).1, ?_, ?_, ?_, ?_⟩
    · intro φ ψ h
      have h1 := RawLimit.congr_sequence (hC φ) (fun j => (u j).action_valid ψ)
        (fun j => (u j).action_linear.respects_test_equiv φ ψ h)
      exact RawLimit.unique h1 (hC ψ)
    · have h1 := RawLimit.congr_sequence (RawLimit.constant (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0))
        (fun j => (u j).action_valid S.zero)
        (fun j => RealCompute.equiv_symm (u j).action_linear.map_zero)
      exact RawLimit.unique (hC S.zero) h1
    · intro φ ψ
      have h1 := RawLimit.congr_sequence (hC (S.add φ ψ))
        (fun j => RealCompute.add_valid ((u j).action_valid φ) ((u j).action_valid ψ))
        (fun j => (u j).action_linear.map_add φ ψ)
      exact RawLimit.unique h1 (tendsTo_add (hC φ) (hC ψ))
    · intro r hr φ
      have h1 := RawLimit.congr_sequence (hC (S.scale r hr φ))
        (fun j => RealCompute.mul_valid hr ((u j).action_valid φ))
        (fun j => (u j).action_linear.map_scale r hr φ)
      exact RawLimit.unique h1 (tendsTo_const_mul (hC φ) hr)
  have hcont : IsContinuousTestAction A hlin.value_valid := by
    intro B
    obtain ⟨order, C, hC0, hbd⟩ := hB B
    refine ⟨order, C, hC0, fun φ hφ b hb hder => ?_⟩
    exact limit_in_interval (I := {lo := -(C * b), hi := C * b}) (hC φ)
      ⟨0, fun j _ => hbd j φ hφ b hb hder⟩
  exact ⟨⟨A, hlin, hcont⟩, fun φ => RealCompute.equiv_refl _ (hC φ).1⟩
