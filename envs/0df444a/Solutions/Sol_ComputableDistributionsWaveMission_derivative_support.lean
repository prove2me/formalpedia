-- Prove2me | solution 1 for ComputableDistributionsWaveMission.derivative_support
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T16:56:17.594801+00:00
-- url     : https://prove2.me/submissions/9a695573-936a-4824-ae8b-b4bccc41b596

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_MissionTargets
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivativeConstruction

open ComputableAnalysis ComputableDistributions

namespace DerivativeSupportAux

/-- A scaled difference of two rational zeros is equivalent to zero. -/
theorem scaled_zero_sub_equiv (c : Rat) :
    (RealCompute.scaleRat c (RealCompute.ofRat 0 - RealCompute.ofRat 0)).Equiv
      (RealCompute.ofRat 0) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have h0 : (RealCompute.scaleRat c (RealCompute.ofRat 0 - RealCompute.ofRat 0)).compute n
      = { lo := 0, hi := 0 } := by
    show RealCompute.scaleRatCompute c _ n = _
    unfold RealCompute.scaleRatCompute
    show (if 0 ≤ c then _ else _) = _
    have hz : Rat.sub 0 0 = 0 := by decide +kernel
    split <;> simp [HSub.hSub, Sub.sub, RealCompute.sub, RealCompute.subCompute, hz]
  rw [h0, RealCompute.ofRat_compute]
  unfold QInterval.Overlaps
  simp

/-- A derivative is zero whenever the function vanishes on a nondegenerate
rational interval around the point. -/
theorem derivative_zero_of_vanishing {f : Rat → RealCompute} {q : Rat} {d : RealCompute}
    (h : BracketDerivative.HasDerivativeAt (fun _ => True) f (RealCompute.ofRat q) d)
    {a b : Rat} (hab : a < b) (haq : a ≤ q) (hqb : q ≤ b)
    (hzero : ∀ r, a ≤ r → r ≤ b → (f r).Equiv (RealCompute.ofRat 0)) :
    d.Equiv (RealCompute.ofRat 0) := by
  have hq : (RealCompute.ofRat q).Valid := RealCompute.ofRat_valid q
  have h0 : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0
  have hla : (RealCompute.ofRat a).Le (RealCompute.ofRat q) := fun _ _ => haq
  have hlb : (RealCompute.ofRat q).Le (RealCompute.ofRat b) := fun _ _ => hqb
  have hA := BracketDerivative.clipped_admissible hq hab hla hlb
  have hA' : BracketDerivative.Admissible (fun _ => True) (RealCompute.ofRat q)
      (BracketDerivative.clipped a b (RealCompute.ofRat q)) :=
    ⟨hA.1, hA.2.1, hA.2.2.1, fun n => ⟨(hA.2.2.2 n).1, fun _ _ _ => trivial⟩⟩
  have hT := RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 _ hA')
  have hfv : ∀ r, (f r).Valid := fun r => h.2.2.1 r trivial
  have hT0 : RawLimit.TendsTo (fun _ => RealCompute.ofRat 0) d :=
    RawLimit.congr_sequence hT (fun _ => h0) (by
    intro n
    have hn := (hA.2.2.2 n)
    have hlo := hn.2 _ Rat.le_refl (Rat.le_of_lt hn.1)
    have hhi := hn.2 _ (Rat.le_of_lt hn.1) Rat.le_refl
    have hsub := RealCompute.sub_equiv (hfv _) h0
      (hfv _) h0 (hzero _ hhi.1 hhi.2) (hzero _ hlo.1 hlo.2)
    have hsc := RealCompute.scaleRat_equiv (r := 1 /
      (((BracketDerivative.clipped a b (RealCompute.ofRat q)).compute n).hi -
        ((BracketDerivative.clipped a b (RealCompute.ofRat q)).compute n).lo)) hsub
    exact RealCompute.equiv_trans
      (BracketDerivative.secants_valid (fun r _ => hfv r) hA' n)
      (RealCompute.scaleRat_valid (RealCompute.sub_valid h0 h0))
      h0 hsc (scaled_zero_sub_equiv _))
  exact RawLimit.unique hT0 (RawLimit.constant _ h0)

end DerivativeSupportAux

theorem solution : ComputableDistributions.TestDerivativeSupportTarget := by
  intro dimension φ B hφ i x hx
  have hpd := φ.partialDerivative (zeroIndex dimension) i x
  have hrep : ∀ r, (replaceCoordinate x i r) i = r := fun r => by
    simp [replaceCoordinate]
  -- find a coordinate where `x` leaves the box
  have hout : ∃ j, ¬ (B.lower j ≤ x j ∧ x j ≤ B.upper j) := by
    apply Classical.byContradiction
    intro hno
    exact hx (fun j => Classical.byContradiction fun hj => hno ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hout
  have key : ∃ a b : Rat, a < b ∧ a ≤ x i ∧ x i ≤ b ∧
      ∀ r, a ≤ r → r ≤ b → ¬ B.Contains (replaceCoordinate x i r) := by
    by_cases hji : j = i
    · subst hji
      by_cases hlo : B.lower j ≤ x j
      · have hup : B.upper j < x j := by
          apply Rat.not_le.mp
          intro h; exact hj ⟨hlo, h⟩
        refine ⟨(B.upper j + x j) / 2, x j + 1, by grind, by grind, by grind, ?_⟩
        intro r hr _ hc
        have := (hc j).2
        rw [hrep] at this
        grind
      · have hlo' : x j < B.lower j := Rat.not_le.mp hlo
        refine ⟨x j - 1, (B.lower j + x j) / 2, by grind, by grind, by grind, ?_⟩
        intro r _ hr hc
        have := (hc j).1
        rw [hrep] at this
        grind
    · refine ⟨x i - 1, x i + 1, by grind, by grind, by grind, ?_⟩
      intro r _ _ hc
      apply hj
      have := hc j
      simpa [replaceCoordinate, hji] using this
  obtain ⟨a, b, hab, ha, hb, hnot⟩ := key
  exact DerivativeSupportAux.derivative_zero_of_vanishing hpd hab ha hb
    (fun r har hrb => hφ _ (hnot r har hrb))
