-- Prove2me | solution 1 for FairReplay.eq_38_39
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T19:49:51.646409+00:00
-- url     : https://prove2.me/submissions/6933a65f-28ca-4cf8-b308-16751e412fdf

import Mathlib
import Definitions.Def_FairReplay_fourWayModel

open MeasureTheory
namespace ReplayPath
open FairReplay
noncomputable section

def differential (p : ℝ) (new : Fin 2 → ℝ) (U : ℝ) : ℤ :=
  let b : Bool → ℤ := fun x => if x then 1 else 0
  (b (fourWayObs ![p,p] new U 1) - b (fourWayObs ![p,p] new U 0)) -
    (b (fourWayObs ![p,p] new U 3) - b (fourWayObs ![p,p] new U 2))

lemma null_zero (p s U : ℝ) : differential p ![p+s,p+s] U = 0 := by
  simp [differential, fourWayObs]

lemma alt_indicator (p s d U : ℝ) (hd : 0 ≤ d) :
    differential p ![p+s+d,p+s] U = if U ∈ Set.Ioc (p+s) (p+s+d) then 1 else 0 := by
  by_cases h1 : U ≤ p+s
  · have h2 : U ≤ p+s+d := by linarith
    simp [differential, fourWayObs, thresholdOut, h1, h2, Set.mem_Ioc, not_lt.mpr h1] <;> by_cases h0 : U ≤ p <;> simp [h0]
  · by_cases h2 : U ≤ p+s+d
    · simp [differential, fourWayObs, thresholdOut, h1, h2, Set.mem_Ioc, lt_of_not_ge h1] <;> by_cases h0 : U ≤ p <;> simp [h0]
    · simp [differential, fourWayObs, thresholdOut, h1, h2, Set.mem_Ioc] <;> by_cases h0 : U ≤ p <;> simp [h0]

lemma interval_mass (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniformTape (Set.Ioc a b) = ENNReal.ofReal (b-a) := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1.le,hx.2.trans hb⟩
  rw [uniformTape, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc]

lemma alt_mass (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p+s+d < 1) :
    uniformTape {U | differential p ![p+s+d,p+s] U = 1} = ENNReal.ofReal d := by
  have he : {U | differential p ![p+s+d,p+s] U = 1} = Set.Ioc (p+s) (p+s+d) := by
    ext U
    simp [alt_indicator p s d U hd.le]
  rw [he,interval_mass _ _ (by linarith) hpsd.le]
  congr 1
  ring

lemma lower_endpoint_control (p s d : ℝ) (hd : 0 ≤ d) :
    differential p ![p+s+d,p+s] (p+s) = 0 := by
  simp [alt_indicator p s d (p+s) hd]

lemma upper_endpoint_control (p s d : ℝ) (hd : 0 < d) :
    differential p ![p+s+d,p+s] (p+s+d) = 1 := by
  rw [alt_indicator p s d (p+s+d) hd.le]
  simp only [Set.mem_Ioc, le_refl, and_true, ite_eq_left_iff, Int.zero_ne_one,
    imp_false, not_not]
  linarith

lemma zero_gap_control (p s U : ℝ) : differential p ![p+s+0,p+s] U = 0 := by
  simpa using null_zero p s U

end
end ReplayPath

theorem solution : (
  ∀ (p s d : Real),
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) p →
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) s →
        @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) d →
          @LT.lt Real Real.instLT
              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) d)
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
            have b := fun (x : Bool) =>
              @ite Int (@Eq Bool x Bool.true) (instDecidableEqBool x Bool.true)
                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)));
            have W := fun (new : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real) (U : Real) =>
              @HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                  (b
                    (FairReplay.fourWayObs
                      (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p
                        (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p
                          (@Matrix.vecEmpty Real)))
                      new U
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)))))
                  (b
                    (FairReplay.fourWayObs
                      (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p
                        (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p
                          (@Matrix.vecEmpty Real)))
                      new U
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))))
                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                  (b
                    (FairReplay.fourWayObs
                      (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p
                        (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p
                          (@Matrix.vecEmpty Real)))
                      new U
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 3)))))
                  (b
                    (FairReplay.fourWayObs
                      (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p
                        (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p
                          (@Matrix.vecEmpty Real)))
                      new U
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2))))));
            And
              (∀ (U : Real),
                @Membership.mem Real (Set Real) (@Set.instMembership Real)
                    (@Set.Icc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                    U →
                  @Eq Int
                    (W
                      (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s)
                        (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) (@Matrix.vecEmpty Real)))
                      U)
                    (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (And
                (∀ (U : Real),
                  @Membership.mem Real (Set Real) (@Set.instMembership Real)
                      (@Set.Icc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                      U →
                    Iff
                      (@Eq Int
                        (W
                          (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) d)
                            (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) (@Matrix.vecEmpty Real)))
                          U)
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                        (@Set.Ioc Real Real.instPreorder (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s)
                          (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                            (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) d))
                        U))
                (@Eq ENNReal
                  (@DFunLike.coe (@MeasureTheory.Measure Real Real.measurableSpace) (Set Real)
                    (fun (x : Set Real) => ENNReal) (@MeasureTheory.Measure.instFunLike Real Real.measurableSpace)
                    FairReplay.uniformTape
                    (@Set.ofPred Real fun (U : Real) =>
                      @Eq Int
                        (W
                          (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) d)
                            (@Matrix.vecCons Real (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) p s) (@Matrix.vecEmpty Real)))
                          U)
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (ENNReal.ofReal d)))
) := by
  intro p s d hp hs hd hpsd
  change (∀ U ∈ Set.Icc (0:ℝ) 1, ReplayPath.differential p ![p+s,p+s] U = 0) ∧
    (∀ U ∈ Set.Icc (0:ℝ) 1, ReplayPath.differential p ![p+s+d,p+s] U = 1 ↔ U ∈ Set.Ioc (p+s) (p+s+d)) ∧
    FairReplay.uniformTape {U | ReplayPath.differential p ![p+s+d,p+s] U = 1} = ENNReal.ofReal d
  refine ⟨fun U _ => ReplayPath.null_zero p s U, ?_, ReplayPath.alt_mass p s d hp hs hd hpsd⟩
  intro U _
  simp [ReplayPath.alt_indicator p s d U hd.le]
